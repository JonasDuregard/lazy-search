{-#LANGUAGE GADTs, DeriveDataTypeable, DeriveFunctor #-}

-- | Efficient size-based search for values satisfying/falsifying a lazy boolean predicate. 
-- Predicates are typically of type @a -> Bool@, although an alternative boolean type called 'Cool' is provided and using it may give faster searches. 
--
-- See "Control.Enumerable" for defining default enumerations of data types (required for searching). 
module Control.Search 
  ( 
  -- * Searching 
  search, sat, ctrex, searchRaw, usearch
  -- * Testing properties
  , test, testTime
  -- * Options for parallel conjunction
  , Options (..)
  , sat', search', ctrex', searchRaw', test', testTime'
  -- * Deep embedded boolean type
  , (&&&), (|||), (==>), nott, true, false 
  , Cool(..)
  , Coolean
  -- * Re-exported
  , module Control.Enumerable
  ) where

import Data.IORef
import Control.Sized
import Control.Enumerable

import System.IO.Unsafe

import Control.Enumerable.Count


import Data.Coolean

import System.Timeout


newCounter :: IO (IO Int)
newCounter = do
  ref <- newIORef 0
  return (atomicModifyIORef ref (\i -> (i+1,i)))

attach :: (IO Int) -> a -> IO (IO Int, a)
attach c a = do
  ref <- newIORef (-1)
  return (readIORef ref, unsafePerformIO $ c >>= writeIORef ref >> return a)



data Value a where
  Pair :: (a,b) -> Value a -> Value b -> Value (a,b)
  Map  :: a -> (b -> a) -> Value b -> Value a
  Unit :: a -> Value a
  -- A value that can potentially be replaced by a larger value
  Alt  :: a -> Value a -> Minimal a -> Value a
  
  -- StrictAlt :: a -> Value a -> (Int -> [a])
  

instance Show a => Show (Value a) where
  show v = "("++ repV v ++ ", " ++ show (plainV v) ++ ")"

instance Functor Value where
  fmap f a = Map (f (plainV a)) f a

  
repV :: Value a -> String
repV (Unit _)      = "1"
repV (Pair _ a b)  = "("++ repV a ++ ", " ++ repV b ++ ")"
repV (Alt _ a _)   = "?"++ repV a
repV (Map a f v)   = "$"++ repV v

plainV :: Value a -> a
plainV (Pair a _ _) = a
plainV (Map a _ _)  = a
plainV (Unit a)     = a
plainV (Alt a _ _)  = a

mkPair :: Value a -> Value b -> Value (a,b)
mkPair (Unit a) (Unit b) = Unit (a,b)
mkPair (Unit a) v        = mkMap ((,) a) v
mkPair v        (Unit b) = mkMap (\a -> (a,b)) v
mkPair v1       v2       = Pair (plainV v1,plainV v2) v1 v2

mkAlt :: Value a -> Minimal a -> Value a
mkAlt v s = Alt (plainV v) v s

mkMap :: (a -> b) -> Value a -> Value b
mkMap f (Unit a)     = Unit (f a)
mkMap f (Map a g v)  = Map (f a) (f . g) v
mkMap f v = Map (f (plainV v)) f v



data Minimal a where -- ADT
  Pay     :: Minimal a  -> Minimal a
  Value   :: Value a    -> Minimal a
  Empty   ::               Minimal a
  deriving Typeable

instance Functor Minimal where
  fmap f (Pay s)    = Pay (fmap f s)
  fmap f (Value v)  = Value (fmap f v)
  fmap _ Empty      = Empty

instance Applicative Minimal where
  pure a = Value (Unit a)
  sf <*> sa = fmap (uncurry ($)) (pair sf sa)

instance Alternative Minimal where
  empty = Empty
  Empty <|> s             = s
  s <|> Empty             = s
  Pay a     <|> Pay b     = Pay (a <|> b)
  Value vf  <|> s         = Value (mkAlt vf s)
  a         <|> Value vf  = Value (mkAlt vf a)

instance Sized Minimal where
  pay   = Pay
  pair Empty _              = Empty
  pair _ Empty              = Empty
  pair (Pay a) b            = Pay (pair a b) 
  pair a (Pay b)            = Pay (pair a b)
  pair (Value f) (Value g)  = Value (mkPair f g)
  
  naturals = pure 0 <|> pay (fmap (+1) naturals)
  
  aconcat []      = empty
  aconcat [s]     = s
  aconcat [s1,s2] = s1 <|> s2
  aconcat ss0 = case extr ss0 of
        ([],m)      -> maybe Empty Value m
        (ss',m)     -> maybe (pay (aconcat ss')) (Value . (`mkAlt` (aconcat ss'))) m
      where
      extr :: [Minimal a] -> ([Minimal a], Maybe (Value a))
      extr (s:ss)            = case s of
        Value v   -> (ss,Just v)
        Empty     -> extr ss
        Pay s'    -> case extr ss of
          (ss',Nothing) -> (s':ss',Nothing)
          (ss',j)       -> (s:ss', j)
      extr _                 = ([], Nothing)

data Observed a = Observed { sizeLeft :: Int, val :: Value a } deriving Functor
instance Show a => Show (Observed a) where
  show = show . val


minimal :: Minimal a -> Int -> Maybe (Observed a)
minimal _          n | n < 0  = Nothing
minimal Empty      _          = Nothing
minimal (Pay s)    n          = minimal s (n-1)
minimal (Value vf) n          = Just (Observed n vf) 




data Relevant a = Relevant 
  {  -- | The order in which this choice was made
     evalOrder  :: Int,  
     -- | The result of fixing this and all earlier choices
     fixed      :: Value a,
     -- | The result of swapping this and fixing earlier choices
     swapped    :: Observed a
  }

(<<) :: Relevant a -> Relevant b -> Bool
r << q = evalOrder r < evalOrder q

merge :: Value a -> Value b -> [Relevant a] -> [Relevant b] -> [Relevant (a,b)]
merge va _  [] r = rsmap (mkPair va) r
merge _  vb r [] = rsmap (`mkPair` vb) r
merge va vb rs@(r:rs') qs@(q:qs') 
      | q << r     = rmap (va `mkPair`) q : merge va (fixed q) rs  qs'
      | otherwise  = rmap (`mkPair` vb) r : merge (fixed r) vb rs' qs

-- Alter a Relevant choice by altering both the swapped and fixed value
rmap :: (Value a -> Value b) -> Relevant a -> Relevant b
rmap f r = r{fixed = f (fixed r), swapped = omap f (swapped r)} where
  omap g o' = o'{val = g (val o')}

rsmap :: (Value a -> Value b) -> [Relevant a] -> [Relevant b]
rsmap f = map (rmap f)


observed :: Observed a -> IO (IO [Observed a], a)
observed o = do
    c <- newCounter
    let go :: Value a -> IO (IO [Relevant a], a)
        go (Pair _ va vb) = do
          (rs, xa) <- go va
          (qs, xb) <- go vb
          return (liftA2 (merge va vb) rs qs, (xa,xb))
        go (Map _ f v)    = do 
          ~(x,a) <- (go v)
          return (fmap (rsmap (fmap f)) x,f a) 
        go (Unit a)       = return (return [], a)
        go (Alt _ v x)    = do
          ~(tr,a) <- go v
          (i, a') <- attach c a
          return (tralt tr i, a')
          where
            tralt tr i = i >>= \n -> case n of
              -1 -> return []
              _  -> case minimal x (sizeLeft o) of 
                      Just nv -> fmap (Relevant n v nv :) tr
                      Nothing -> tr
    fmap (\(a,b) -> (fmap fx a, b)) $ go (val o) where
        fx :: [Relevant a] -> [Observed a]
        fx rs = reverse (map swapped rs)

observedc :: Observed a -> IO (IO Int, IO [Observed a], a)
observedc o = do
    ref <- newIORef 0
    let c = atomicModifyIORef ref (\i -> (i+1,i))
    let go :: Value a -> IO (IO [Relevant a], a)
        go (Pair _ va vb) = do
          (rs, xa) <- go va
          (qs, xb) <- go vb
          return (liftA2 (merge va vb) rs qs, (xa,xb))
        go (Map _ f v)    = do 
          ~(x,a) <- (go v)
          return (fmap (rsmap (fmap f)) x,f a) 
        go (Unit a)       = return (return [], a)
        go (Alt _ v x)    = do
          ~(tr,a) <- go v
          (i, a') <- attach c a
          return (tralt tr i, a')
          where
            tralt tr i = i >>= \n -> case n of
              -1 -> return []
              _  -> case minimal x (sizeLeft o) of 
                      Just nv -> fmap (Relevant n v nv :) tr
                      Nothing -> tr
    fmap (\(a,b) -> (readIORef ref, fmap fx a, b)) $ go (val o) where
        fx :: [Relevant a] -> [Observed a]
        fx rs = reverse (map swapped rs)








type State a = [[Observed a]]
type StateP a = [(Sched, [Observed a])]


-- Sequential search
{-#INLINE stepD #-}
stepD :: (a -> Bool) -> State a -> IO ((Bool, a), State a)
stepD q ((o:os):s) = do
  let s' = if null os then s else os:s  -- Pick a value from the stack
  (ins, a) <- observed o                -- Get an observable copy
  let b = q a
  () <- b `seq` return ()
  os' <- ins                            -- Swap all choices
  return ((b, plainV (val o)), if null os' then s' else os':s')
stepD _ _             = error $ "Invalid state"


searchRawD :: Enumerable a => Int -> (a -> Bool) -> IO [(Bool,a)]
searchRawD n q = do
  let mo = minimal local n
  maybe (return []) (\o -> lazy q [[o]]) mo
  where
    lazy :: (a -> Bool) -> State a -> IO [(Bool,a)]
    lazy _ [] = return []
    lazy q' s = do
      (ba,s') <- stepD q' s
      fmap (ba:) (unsafeInterleaveIO $ lazy q' s')

-- Fair Parallel conjunction
stepF :: (a -> Cool) -> StateP a -> IO ((Bool, a), StateP a)
stepF q ((sc,(o:os)):s) = do
  let s' = if null os then s else (sc,os):s  -- Pick a value from the stack
  (ins, a) <- observed o                     -- Get an observable copy
  let (sc',b) = par sc (q a)
  () <- b `seq` return ()
  os' <- ins                                 -- Swap all choices
  return ((b, plainV (val o)), if null os' then s' else ((sc',os'):s'))
stepF _ _             = error $ "Invalid state"


searchRawF :: Enumerable a => Int -> (a -> Cool) -> IO [(Bool,a)]
searchRawF n q = do
  let mo = minimal local n
  maybe (return []) (\o -> lazy q [(sched0, [o])]) mo
  where 
    lazy :: (a -> Cool) -> StateP a -> IO [(Bool,a)]
    lazy _ [] = return []
    lazy q' s = do
      (ba,s') <- stepF q' s
      fmap (ba:) (unsafeInterleaveIO $ lazy q' s')



-- Short-circuiting sequential search
stepO :: (a -> Cool) -> StateP a -> IO ((Bool, a), StateP a)
stepO q ((sc,(o:os)):s) = do
  let s' = if null os then s else (sc,os):s  -- Pick a value from the stack
  
  let (sc', _) = lookahead sc (q (plainV (val o)))
  
  (ins, a) <- observed o                     -- Get an observable copy
  let b = run sc' (q a)
  
  () <- b `seq` return ()
  os' <- ins                                 -- Swap all choices
  return ((b, plainV (val o)), if null os' then s' else ((sc',os'):s'))
stepO _ _             = error $ "Invalid state"

searchRawO :: Enumerable a => Int -> (a -> Cool) -> IO [(Bool,a)]
searchRawO n q = do
  let mo = minimal local n
  maybe (return []) (\o -> lazy [(sched0, [o])]) mo
  where
    -- lazy :: StateP a -> IO [(Bool,a)]
    lazy [] = return []
    lazy s = do
      (ba,s') <- stepO q s
      fmap (ba:) (unsafeInterleaveIO $ lazy s')





-- Short-circuiting parallel search
stepOF :: (a -> Cool) -> StateP a -> IO ((Bool, a), StateP a)
stepOF q ((sc,(o:os)):s) = do
  let s' = if null os then s else (sc,os):s  -- Pick a value from the stack
  
  let (sc', _) = lookahead sc (q (plainV (val o)))
  (ins, a) <- observed o                     -- Get an observable copy
  let (sc'',b) = par sc' (q a)  
  () <- b `seq` return ()
  os' <- ins                                 -- Swap all choices
  return ((b, plainV (val o)), if null os' then s' else ((sc'',os'):s'))
stepOF _ _             = error $ "Invalid state"

searchRawOF :: Enumerable a => Int -> (a -> Cool) -> IO [(Bool,a)]
searchRawOF n q = do
  let mo = minimal local n
  maybe (return []) (\o -> lazy [(sched0, [o])]) mo
  where
    -- lazy :: StateP a -> IO [(Bool,a)]
    lazy [] = return []
    lazy s = do
      (ba,s') <- stepOF q s
      fmap (ba:) (unsafeInterleaveIO $ lazy s')

-- Subset-minimize
stepOS :: (a -> Cool) -> StateP a -> IO ((Bool, a), StateP a)
stepOS q ((sc,(o:os)):s) = do
  let s' = if null os then s else (sc,os):s  -- Pick a value from the stack
  
  (c,_, a1) <- observedc o                 -- Get an observable copy
  (sc', _) <- subsetsc c sc (q a1)
  
  (ins, a) <- observed o                     -- Get an observable copy
  let b = run sc' (q a)
  
  () <- b `seq` return ()
  os' <- ins                                 -- Swap all choices
  return ((b, plainV (val o)), if null os' then s' else ((sc',os'):s'))
stepOS _ _             = error $ "Invalid state"

searchRawOS :: Enumerable a => Int -> (a -> Cool) -> IO [(Bool,a)]
searchRawOS n q = do
  let mo = minimal local n
  maybe (return []) (\o -> lazy [(sched0, [o])]) mo
  where
    lazy [] = return []
    lazy s = do
      (ba,s') <- stepOS q s
      fmap (ba:) (unsafeInterleaveIO $ lazy s')


-- OS + parallel
stepOSF :: (a -> Cool) -> StateP a -> IO ((Bool, a), StateP a)
stepOSF q ((sc,(o:os)):s) = do
  let s' = if null os then s else (sc,os):s  -- Pick a value from the stack
  
  
  (c,_, a1) <- observedc o                 -- Get an observable copy
  (sc', _)  <- subsetsc c sc (q a1)
  
  (ins, a) <- observed o                     -- Get an observable copy
  let (sc'',b) = par sc' (q a)
  
  () <- b `seq` return ()
  os' <- ins                                 -- Swap all choices
  return ((b, plainV (val o)), if null os' then s' else ((sc'',os'):s'))
stepOSF _ _             = error $ "Invalid state"

searchRawOSF :: Enumerable a => Int -> (a -> Cool) -> IO [(Bool,a)]
searchRawOSF n q = do
  let mo = minimal local n
  maybe (return []) (\o -> lazy [(sched0, [o])]) mo
  where
    lazy [] = return []
    lazy s = do
      (ba,s') <- stepOSF q s
      fmap (ba:) (unsafeInterleaveIO $ lazy s')


{-
stepI :: (a -> Cool) -> StateP a -> IO ((Bool, a), StateP a)
stepI q ((sc,(o:os)):s) = do
  let s' = if null os then s else (sc,os):s  -- Pick a value from the stack

  (ins, a) <- observed o                     -- Get an observable copy
  
  let c = prune (q (plainV (val o))) (q a)
  
  let b = runInterl (snd c)
  
  () <- b `seq` return ()
  os' <- ins                                 -- Swap all choices
  return ((b, plainV (val o)), if null os' then s' else ((sc,os'):s'))
stepI q s               = error $ "Invalid state"

searchRawI :: Enumerable a => Int -> (a -> Cool) -> IO [(Bool,a)]
searchRawI n q = do
  let mo = minimal local n
  maybe (return []) (\o -> lazy [(sched0, [o])]) mo
  where
    lazy [] = return []
    lazy s = do
      (ba,s') <- stepI q s
      fmap (ba:) (unsafeInterleaveIO $ lazy s')
-}

-- | Options for parallel conjunction strategies. Only matters for 
-- predicates using the @Cool@ data type instead of Bool.
data Options 
  = 
    -- | Sequential
    D    
    -- | Optimal Short-circuiting
  | O
    -- | Parallel (fair)
  | F
    -- | Optimal Short-circuiting and fairness
  | OF
    -- | Optimal Short-circuiting and choice-subset detection
  | OS    
    -- | Subset choice short-circuiting
  | OSF
  deriving (Show, Read, Eq, Enum)

defOptions :: Coolean cool => (a -> cool) -> Options
defOptions p | isCool p = OF
defOptions _            = D

-- | Lazily finds all non-isomorphic (w.r.t. laziness) inputs to a 
-- predicate and returns them along with the result of the predicate. 
searchRaw :: (Enumerable a, Coolean cool) => Int -> (a -> cool) -> IO [(Bool,a)]
searchRaw n p = searchRaw' (defOptions p) n p

searchRaw' :: (Enumerable a, Coolean cool) => Options -> Int -> (a -> cool) -> IO [(Bool,a)]
searchRaw' D   n p = searchRawD  n (toBool . p)
searchRaw' O   n p = searchRawO  n (toCool . p)
searchRaw' F   n p = searchRawF  n (toCool . p)
searchRaw' OF  n p = searchRawOF n (toCool . p)
searchRaw' OS  n p = searchRawOS  n (toCool . p)
searchRaw' OSF  n p = searchRawOSF n (toCool . p)

-- | Lazily finds all (non-isomorphic) values of or below a given size that satisfy a predicate. 
search :: (Enumerable a, Coolean cool) => Int -> (a -> cool) -> IO [a]
search n p = search' (defOptions p) n p

search' :: (Enumerable a, Coolean cool) => Options -> Int -> (a -> cool) -> IO [a]
search' o n q = do
  xs <- searchRaw' o n q
  return [a | (b,a) <- xs, b]

-- | Is there a value of or below a given size that satisfies this predicate?
sat :: (Enumerable a, Coolean cool) => Int -> (a -> cool) -> Bool
sat n p = sat' (defOptions p) n p

sat' :: (Enumerable a, Coolean cool) => Options -> Int -> (a -> cool) -> Bool
sat' o n q = unsafePerformIO (fmap (not . null) (search' o n q))

-- | Unsafe version of search. Non-deterministic for some predicates. 
usearch :: Enumerable a => Int -> (a -> Bool) -> [a]
usearch n p = usearch' (defOptions p) n p

usearch' :: Enumerable a => Options -> Int -> (a -> Bool) -> [a]
usearch' o n q = unsafePerformIO (search' o n q)


-- | Find a counterexample to the given predicate, of or below a given size. 
-- If no counterexample is found, the number of performed executions of the predicate is returned. 
ctrex :: (Coolean cool, Enumerable a) => Int -> (a -> cool) -> IO (Either Integer a)
ctrex n p = ctrex' (defOptions p) n p

ctrex' :: (Coolean cool, Enumerable a) => Options -> Int -> (a -> cool) -> IO (Either Integer a)
ctrex' o n0 q0 = do 
  let q = nott . q0
  xs <- searchRaw' o n0 q
  return (go xs 0)
  where go []           n      = Left n
        go ((b,a):_)    _ | b  = Right a
        go (_    :xs')  n      = go xs' (n+1)
 
-- Count the domain of a function
countdom :: Enumerable a => (a -> b) -> Count a
countdom _ = global

test' :: (Coolean cool, Enumerable a, Show a) => Options -> (a -> cool) -> IO ()
test' o q = go 0 0 (count (countdom q)) where
  go _ _   []     = putStrLn "No counterexample found"
  go n acc (c:cs) = do
    let acc' = acc + c 
    putStrLn $ "Testing to size "++ show n ++ ", worst case "++show acc'++" tests" 
    e <- ctrex' o n q
    case e of 
      Left t   -> putStrLn ("No counterexample found in "++show t++" tests") >> putStrLn "" >> 
                    go (n+1) acc' cs
      Right x  -> putStrLn "Counterexample found:" >> print x

-- | SmallCheck-like test driver. Tests a property with gradually increasing sizes until a conunterexample is found. For each size, it shows the worst case number of tests required 
-- (if the predicate is fully eager).
test :: (Coolean cool, Enumerable a, Show a) => (a -> cool) -> IO ()
test p = test' (defOptions p) p


-- | Stop testing after a given number of seconds
testTime :: (Coolean cool, Enumerable a, Show a) => Int -> (a -> cool) -> IO ()
testTime t p = testTime' (defOptions p) t p
  
testTime' :: (Coolean cool, Enumerable a, Show a) => Options -> Int -> (a -> cool) -> IO ()
testTime' o t p = do
  mu <- timeout (t*1000000) (test' o p)
  case mu of Nothing  -> putStrLn "Timed out"
             Just{}   -> return ()

{-
testall :: (Coolean cool, Enumerable a, Show a) => Options -> (a -> cool) -> IO ()
testall o q = go 0 0 (count (countdom q)) where
  go n _   []     = putStrLn "No counterexample found"
  go n acc (c:cs) = do
    let acc' = acc + c 
    putStrLn $ show n ++ " ("++show acc'++")" 
    t <- fmap length (searchRaw' o n q)
    print t
    go (n+1) acc' cs



-- Testing framework
data Pred where 
  Pred :: (Enumerable a, Show a) => (a -> Cool) -> Pred

class Predicate p where
  predicate :: p -> Pred
  puncurry  :: (Enumerable a, Show a) => (a -> p) -> Pred

instance (Predicate b, Enumerable a, Show a) => Predicate (a -> b) where
  predicate = puncurry
  puncurry f = predicate (uncurry f)

instance Predicate Cool where
  predicate x = Pred (\() -> x)
  puncurry    = Pred


testN :: Predicate p => Int -> p -> IO (Maybe String)
testN n p = case predicate p of Pred x -> testN' n x

testN' :: (Show a, Enumerable a) => Int -> (a -> Cool) -> IO (Maybe String)
testN' n p = do
  xs <- search' OF n p
  case xs of
    []    -> return Nothing
    (x:_) -> return (Just (show x))

-}
