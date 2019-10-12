
-- | Proper documentation is TBD
module Data.Coolean
 ( Cool(..)
 -- * Overloaded parallel operators
 , Coolean(..)
 , true, false, nott
 , (&&&), (|||), (==>)
 -- * Overloaded sequential operators
 , (!&&), (!||), (!=>)
 -- * Consumers
 , Sched(..), sched0
 , run, lookahead, par, subsetsc
 ) where

import Control.Exception
import Data.IORef
import System.IO.Unsafe

-- import Data.Tree

-- | Concurrent booleans. Writing properties with the Cool data type often yields faster searches compared to Bool. 
data Cool = Atom Bool
          | Not Cool
          | And Cool Cool
          -- | Sequential conjunction, the second operator is not evaluated unless the first is true. 
          | Seq Cool Cool
          deriving Show

-- Class based construction
true :: Cool
true = Atom True

false :: Cool
false = Atom False

-- | Commutative conjunction
(&&&) :: (Coolean a, Coolean b) => a -> b -> Cool
a &&& b = toCool a <&> toCool b

infixr 3 &&&

-- | Commutative disjunction
(|||) :: (Coolean a, Coolean b) => a -> b -> Cool
a ||| b = toCool a <||> toCool b

infixr 2 |||

-- | Negation
nott :: Coolean a => a -> Cool
nott a = Not (toCool a)

-- | Parallel implication
(==>) :: (Coolean a, Coolean b) => a -> b -> Cool
a ==> b = Not (toCool a <&> Not (toCool b))

infixr 0 ==>

-- | Sequential conjunction. Does not evaluate second operand unless first is True. 
(!&&) :: (Coolean a, Coolean b) => a -> b -> Cool
a !&& b = toCool a `Seq` toCool b

-- | Sequential disjunction. Does not evaluate second operand unless first is True. 
(!||) :: (Coolean a, Coolean b) => a -> b -> Cool
a !|| b = Not (Not (toCool a) `Seq` Not (toCool b))

-- | Sequential implication. Does not evaluate second operand unless first is True. 
(!=>) :: (Coolean a, Coolean b) => a -> b -> Cool
a !=> b = Not (toCool a `Seq` Not (toCool b))


-- | Provides better interoperability between Bool and Cool by overloading operators. 
class Coolean b where
  toCool :: b -> Cool
  toBool :: b -> Bool
  isCool :: (a -> b) -> Bool

instance Coolean Cool where 
  toCool = id
  toBool (And a b) = toBool a && toBool b
  toBool (Seq a b) = toBool a && toBool b
  toBool (Not a)   = not (toBool a)
  toBool (Atom a)  = a
  isCool _ = True

instance Coolean Bool where 
  toCool = Atom
  toBool = id
  isCool _ = False


-- Explicit construction
(<&>) :: Cool -> Cool -> Cool
(<&>) = And

(<&) :: Bool -> Cool -> Cool
a <& b = Atom a <&> b

(&>) :: Cool -> Bool -> Cool
a &> b = a <&> Atom b

(&) :: Bool -> Bool -> Cool
a & b = Atom a <&> Atom b


a <||> b = Not (Not a <&> Not b)


-- Consumers
data Sched = Flip Bool Sched Sched
--           | Fixed
           | Unsched
           deriving (Show, Eq)

-- instance Show Sched where show = drawTree . toTree

split :: Sched -> Sched
split Unsched = Flip False Unsched Unsched
split s   = s

sched0 = Unsched

-- toTree :: Sched -> Tree String
-- toTree Unsched = Node "*" []
-- toTree (Flip b s1 s2) = Node (show b) [toTree s1, toTree s2]


-- Run the given schedule
run :: Sched -> Cool -> Bool
run (Unsched) c     = toBool c
run s@(Flip b s1 s2) c = case c of
  Atom b     -> b
  Not c      -> not (run s c)
  Seq c1 c2  -> run s1 c1 && run s2 c2
  And c1 c2
    | b         -> run s2 c2 && run s1 c1
    | otherwise -> run s1 c1 && run s2 c2


-- Returns a schedule with optimal short-circuiting behaviour
lookahead :: Sched -> Cool  -> (Sched, Bool)
lookahead s c = case c of
  Atom b     -> (s,b)
  Not c      -> fmap not (lookahead s c)
  Seq c1 c2  -> go (lookahead s1 c1) (lookahead s2 c2)
    where
    (Flip b s1 s2) = split s
    go (s1',r1) ~(s2',r2) = case r1 of
      True   -> case r2 of 
        True   -> (Flip False s1' s2', True)    -- Set to unflipped if True
        False  -> (Flip True  s1 s2', False)
      False  -> (Flip b s1' s2, False)

    -- (Flip b s1' s2', r1 && r2)
    -- where (s1', r1) = lookahead s1 c1
    --      (s2', r2) = lookahead s2 c2
    --      (Flip b s1 s2) = split s
  And c1 c2
    | b         -> go (\b' -> flip (Flip b')) (lookahead s2 c2) (lookahead s1 c1)
    | otherwise -> go (\b' -> Flip b')        (lookahead s1 c1) (lookahead s2 c2)
    where
    (Flip b s1 s2) = split s
    go flp (s1',r1) ~(s2',r2) = case r1 of
      True   -> case r2 of 
        True   -> (flp False s1' s2', True)    -- Set to unflipped if True
        False  -> (flp (not b) s1 s2', False)
      False  -> (flp b s1' s2, False)




-- Flip all evaluated parallel conjunctions
par :: Sched -> Cool -> (Sched, Bool)
par s c = case c of
  Atom b     -> (s,b)
  Not c      -> fmap not (par s c)
  Seq c1 c2  -- -> (Flip b s1' s2', r1 && r2)
    | b         -> go (\b' -> flip (Flip b')) (par s2 c2) (par s1 c1)
    | otherwise -> go (\b' -> Flip b')        (par s1 c1) (par s2 c2)
    where
    (Flip b s1 s2) = split s
    go flp (s1',r1) ~(s2',r2) = case r1 of
      True   -> case r2 of 
        True   -> (flp b s1' s2', True)       -- Flip here?
        False  -> (flp b s1 s2', False)
      False  -> (flp b s1' s2, False)
  And c1 c2
    | b         -> go (\b' -> flip (Flip b')) (par s2 c2) (par s1 c1)
    | otherwise -> go (\b' -> Flip b')        (par s1 c1) (par s2 c2)
    where
    (Flip b s1 s2) = split s
    go flp (s1',r1) ~(s2',r2) = case r1 of
      True   -> case r2 of 
        True   -> (flp (False) s1' s2', True)       -- Flip here?
        False  -> (flp (not b) s1 s2', False)
      False  -> (flp (not b) s1' s2, False)




-- Returns a schedule with optimal short-circuiting behaviour and 
-- giving preference to choice-subset operands
subsetsc :: IO Int -> Sched -> Cool -> IO (Sched, Bool)
subsetsc io s0 c0 = go s0 c0 where
  go s c = case c of
    Atom b      -> return (s,b)
    Not c'      -> fmap (fmap not) (go s c')
    Seq c1 c2  -> do 
      (s1', r1) <- go s1 c1
      (s2', r2) <- go s2 c2
      return (Flip b s1' s2', r1 && r2)
      where (Flip b s1 s2) = split s
    And c1 c2
      | b         -> go' (\b' -> flip (Flip b')) (go s2 c2) (go s1 c1)
      | otherwise -> go' (\b' -> Flip b')        (go s1 c1) (go s2 c2)
      where
--      unchanged s1' s2' | b = Flip 
      (Flip b s1 s2) = split s
      go' flp m1 m2 = do
        (s1',r1) <- m1 
        case r1 of
          True   -> do
            (s2',r2) <- m2
            case r2 of 
              True   -> return (flp False s1' s2', True)    -- Set to unflipped if True
              False  -> return (flp (not b) s1 s2', False)
          False  -> do
            n <- io
            (s2',r2) <- m2

            case r2 of 
              True  -> return (flp b s1' s2, False)
              False -> do
                n' <- io
                if (n' > n) -- The other operand made at least one distinct choice
                  then return (flp b s1' s2, False) 
                  else return (flp (not b) s1 s2', False)

-- measure :: IO Int -> Sched -> Cool



{-
suspending :: IORef (Map ThreadId (ThreadId, ThreadId)) -> IORef (Map ThreadId Integer) -> Cool -> IO Bool
suspending threads ref c0 = do 
  mv <- newEmptyMVar
  forkIO (go (putMVar mv) c0)
  takeMVar mv
  
  where
  go :: (Bool -> IO ()) -> Cool -> IO ()
  go res c = case c of
    Not c'     -> go (res . not) c'
    And c1 c2  -> do
      mv <- newEmptyMVar 
      let res' = putMVar mv
      t <- myThreadId
      t1 <- forkIO (go res' c1)
      t2 <- forkIO (go res' c2)
      atomicModifyIORef threads (\m -> (M.insert t (t1,t2) m,()))
      b1 <- takeMVar mv
      let cleanup = do 
            ts <- fmap (`clean` (t1,t2)) (readIORef threads)
            mapM killThread ts
          ret b = cleanup >> res b
      case b1 of 
        False  -> ret False
        True   -> do
          b2 <- takeMVar mv
          case b2 of 
            False  -> ret False
            True   -> ret True
    Atom b     -> evaluate b >>= res


clean :: Map ThreadId (ThreadId, ThreadId) -> (ThreadId, ThreadId) -> [ThreadId]
clean m (t1,t2) = t1:t2:(r t1 ++ r t2)
  where r t = maybe [] id (fmap (clean m) (M.lookup t m))

-}
{-

runInterl :: Cool -> Bool
runInterl = unRes . interl

data Res = Now Bool | Later Res
unRes :: Res -> Bool
unRes (Now b)    = b
unRes (Later x)  = unRes x


interl :: Cool -> Res
interl (Not c)     = Later (interl c) -- Negating consumes an action
interl (And c1 c2) = mer (interl c1) (interl c2) where
{-  mer :: Res -> Res -> Res
  mer r1 r2 = case r1 of
    Now False -> Now False
    Now True  -> r2
    Later r1' -> Later (mer r2 r1') -}
  mer :: Res -> Res -> Res
  mer (Now False) _           = Now False
  mer _           (Now False) = Now False
  mer (Now True)  (Now True)  = Now True
  mer (Later r1') (Later r2') = Later (mer r1' r2')
interl (Atom b)    = Now b
interl (Seq c1 c2) = seqi (interl c1) (interl c2) where 
  seqi (Now False) r2 = Now False
  seqi (Now True)  r2 = r2
  seqi (Later r1') r2 = Later (seqi r1' r2)


prune :: Cool -> Cool -> (Bool,Cool)
prune (Atom a)     c2            = (a, c2)
prune (Not c1)     ~(Not d1)     = case prune c1 d1 of (b,c) -> (not b, Not c)
prune (And c1 c2)  ~(And d1 d2)  = case prune c1 d1 of
      (False, p)  -> (False, p)
      (True,  p)  -> case prune c2 d2 of
        (False, q) -> (False, q)
        (True,  q) -> (True, Seq p q)
prune (Seq c1 c2)  ~(Seq d1 d2)  = case prune c1 d1 of
      (False, p)  -> case prune c2 d2 of
        (False, q) -> (False, And p q)
        (True, q)  -> (False, p)
      (True,  p)  -> case prune c2 d2 of
        (False, q) -> (False, q)
        (True,  q) -> (True, Seq p q)



-- Check that the schedule is optimal
rerun :: Sched -> Cool -> Maybe Bool
rerun Unsched c       = Just (toBool c) -- Should only be Not and Atom
rerun s@(Flip b s1 s2) c = case c of
  Atom b     -> Just b
  Not c      -> fmap not (rerun s c)
  Seq c1 c2  -> rerun s1 c1 && run s2 c2
  And c1 c2
    | b         -> rerun s2 c2 &&&& rerun s1 c1
    | otherwise -> rerun s1 c1 &&&& rerun s2 c2
  where
    Just False &&&& _          = Just False
    Just True  &&&& Just True  = Just True
    _          &&&& _          = Nothing
-}
  

{-
lazify :: Cool -> Cool -> (Bool, Bool)
lazify (Atom a)   ~(Atom x)   = (a,x)
lazify (Not a)    ~(Not x)    = case lazify a x of (b1,b2) -> (not b1, not b2)
lazify (And a b)  ~(And x y)  
  = case lazify a x of
      (False, p)  -> (False, p)
      (True,  p)  -> case lazify b y of
        (False, q) -> (False, q)
        (True,  q) -> (True, p && q)

coolio :: Cool -> Cool -> Cool -> (Bool, Bool, Bool)
coolio (Atom a) ~(Atom x) ~(Atom p) = (a,x,p)
coolio (And a b) ~(And x y) ~(And p q)  
  = case coolio a x p of
      (False, rx, rp)  -> (False, rx, rp)
      (True, rx, rp)   -> case coolio b y q of
        (False, ry, rq) -> (False, ry, rq)
        (True, ry, rq)  -> (True, rx && ry, rp && rq)



data UnCool = UnCool deriving (Show,Read)
instance Exception UnCool

unCool :: a -> IO (IO Bool, a)
unCool a = do
  r <- newIORef False
  let toggle = atomicModifyIORef r (\b -> (not b, b))
      a'     = unsafeDupablePerformIO $ do
        b <- readIORef r
        print b
        if b then return a else throw UnCool
  
  return (toggle, a')


-- unCool :: a

isCool :: Bool -> Bool
isCool b = unsafeDupablePerformIO $ do
  catch (b `seq` return True) (\UnCool -> return False)


test = do
  (tog,a) <- unCool 1
  let x = Just a
  catch (x == Just 1 `seq` print True) (\UnCool -> print "Cool")
  tog -- >>= print
  catch (x == Just 1 `seq` print True) (\UnCool -> print "Not Cool")
  
  
-}
  
  
-- uncool 
