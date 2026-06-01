{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FunctionalDependencies #-}

module ShortestPath where

import           Control.Monad
import           Control.Monad.Cont
import           Control.Monad.Identity (runIdentity)
import           Control.Monad.State
import           Data.Function
import           Data.Functor ((<&>))
import           Data.HashMap.Strict as H hiding (foldr)
import           Data.Hashable
import qualified Data.Matrix as M
import qualified Data.Vector as V
import           Language.Haskell.TH
import           Zoo

--
-- Memoization & Let-Insertion
--

type SMemo r k v = StateT (H.HashMap k v) (Cont r)
runSMemo :: SMemo r k v r -> r
runSMemo = evalCont . flip evalStateT H.empty

class Letable r b v | b -> v r where
  mkVar :: v -> b
  mkLet :: b -> (v -> r) -> r
genlet :: Letable r b v => b -> SMemo r a v v
genlet b = lift (shift (\k -> return $ mkLet b (\v -> k v)))
  where shiftT :: Monad m => ((a -> m r) -> ContT r m r) -> ContT r m a
        shiftT f = ContT (evalContT . f)
        shift :: ((a -> r) -> Cont r r) -> Cont r a
        shift f = shiftT (f . (runIdentity .))
        {-# INLINE shiftT #-}
        {-# INLINE shift #-}
{-# INLINE genlet #-}

memo :: (Hashable a, Letable r b v) => a -> b -> SMemo r a v v
memo a b = do
  m <- gets (H.lookup a)
  case m of
    Just v' -> return v'
    Nothing -> do
      v' <- genlet b
      modify' (insert a v')
      return v'

-- data PairF f a x = PairF (f x) a
-- instance Functor f => Functor (PairF f a) where
--   fmap f (PairF fx a) = PairF (fmap f fx) a
--   {-# INLINE fmap #-}
-- instance (Monad m, Dist f m) => Dist (PairF f a) m where
--   dist (PairF fmx a) = (`PairF` a) <$> dist fmx
-- memoize :: (Hashable a, Letable r b v)
--         => (f b -> b, a -> f a)
--         -> ( PairF f a b -> SMemo r a v b
--            , a -> SMemo r a v (PairF f a a))
-- memoize (φ, ψ) = (φ', ψ')
--   where ψ'           a  = return (PairF (ψ a) a)
--         φ' (PairF fb a) = mkVar <$> memo a (φ fb)
--         {-# INLINE ψ' #-}
--         {-# INLINE φ' #-}
-- {-# INLINE memoize #-}

data CacheTest f a v x
  = CaMiss (f x) a
  | CaHit v
instance Functor f => Functor (CacheTest f a b) where
  fmap f (CaMiss fx a) = CaMiss (fmap f fx) a
  fmap _ (CaHit  b)    = CaHit b
  {-# INLINE fmap #-}
instance (Monad m, Dist f m) => Dist (CacheTest f a b) m where
  dist (CaMiss fmx a) = (`CaMiss` a) <$> dist fmx
  dist (CaHit b)      = return (CaHit b)
  {-# INLINE dist #-}
memoize :: (Hashable a, Letable r b v)
        => (f b -> b, a -> f a)
        -> ( CacheTest f a v b -> SMemo r a v b
           , a -> SMemo r a v (CacheTest f a v a))
memoize (φ, ψ) = (φ', ψ')
  where ψ' a  = do
          m <- gets (H.lookup a)
          return $ case m of
            Just v  -> CaHit v
            Nothing -> CaMiss (ψ a) a
        φ' (CaMiss fb a) = mkVar <$> memo a (φ fb)
        φ' (CaHit v)     = return (mkVar v)
        {-# INLINE ψ' #-}
        {-# INLINE φ' #-}
{-# INLINE memoize #-}

--
-- Unrolling
--

data Trail w x = TrLeaf w | TrNode x x x
  deriving (Show)
instance Functor (Trail w) where
  fmap _ (TrLeaf w) = TrLeaf w
  fmap f (TrNode x y z) = TrNode (f x) (f y) (f z)
  {-# INLINE fmap #-}
instance Monad m => Dist (Trail w) m where
  dist tr = case tr of
    TrLeaf w -> return (TrLeaf w)
    TrNode x y z -> liftM3 TrNode x y z
  {-# INLINE dist #-}
instance Show w => Show (Fix (Trail w)) where show = show . out

data Weight w = Wt w | WInf deriving Functor
instance Show (Weight w) where
  show WInf = "WInf"
  show _    = "Wt"
ψTrail :: (Int -> Int -> Weight w)
        -> (Int, Int, Int) -> Trail (Weight w) (Int, Int, Int)
ψTrail w (i, j, k)
  | k == 0 = TrLeaf (w i j)
  | otherwise = TrNode (i, j, k') (i, k, k') (k, j, k')
  where k' = k - 1
{-# INLINE ψTrail #-}

data Term w v x
  = Inf     | Weight w
  | Var v   | Let x (v -> x)
  | Min x x | Add x x
  deriving Functor

τUnroll :: forall w v x. (Term w v x -> x) -> Trail (Weight w) x -> x
τUnroll φ tr = case tr of
  TrLeaf WInf -> φ Inf
  TrLeaf (Wt w) -> φ (Weight w)
  TrNode x y z -> φ (Min x (φ (Add y z)))
{-# INLINE τUnroll #-}

--
-- Partial Evaluation
--

data PE v x = StInf | DyAtom v | Dy x deriving Functor

toDy :: (Term w v x -> x) -> PE v x -> x
toDy φ e = case e of
  StInf    -> φ Inf
  DyAtom v -> φ (Var v)
  Dy x     -> x
{-# INLINE toDy #-}

τPE :: forall w v x. (Term w v x -> x) -> Term w (PE v v) (PE v x) -> PE v x
τPE φ t = case t of
  Inf -> StInf
  Weight w -> Dy (φ (Weight w))
  Var v -> φ . Var <$> v
  Let StInf h -> h StInf
  Let (DyAtom v) h -> h (DyAtom v)
  Let (Dy x) h -> Dy (φ (Let x (\v -> toDy φ (h (DyAtom v)))))
  Min StInf x -> x; Min x StInf -> x
  Min a b -> Dy (φ (Min (toDy φ a) (toDy φ b)))
  Add StInf _ -> StInf; Add _ StInf -> StInf
  Add a b -> Dy (φ (Add (toDy φ a) (toDy φ b)))
{-# INLINE τPE #-}

--
-- Code Generation
--

φGen :: Term ExpQ ExpQ ExpQ -> ExpQ
φGen t = case t of
  Weight w -> w
  Var name -> name
  Let x h  -> [| let d = $x in $(h [|d|]) |]
  Min a b  -> [| min $a $b |]
  Add a b -> [| $a + $b |]
  Inf -> [| undefined |]
{-# INLINE φGen #-}

--
-- Code Analysis
--

newtype Point = Point (Int, Int) deriving Show

instance Semigroup Point where
  Point (a, b) <> Point (c, d) = Point (a + c, b + d)
instance Monoid Point where mempty = Point (0, 0)

φCount :: Term w Point Point -> Point
φCount t = case t of
  Var v    -> v
  Let x h  -> x <> h mempty
  Min a b  -> a <> b <> Point (1, 0)
  Add a b  -> a <> b <> Point (0, 1)
  _        -> mempty
{-# INLINE φCount #-}

--
-- Generator
--

shortestPath :: Int -> Int -> Int -> M.Matrix (Weight Int) -> ExpQ
shortestPath n s t mat = [| \ v -> $(unwrapPE (runSMemo (output [|v|])))|]
  where
    w  :: ExpQ -> Int -> Int -> Weight ExpQ
    w v i j = M.getElem i j mat <&> \idx -> [| $v V.! idx |]
    output :: ExpQ
           -> SMemo (PE ExpQ ExpQ) (Int, Int, Int) (PE ExpQ ExpQ) (PE ExpQ ExpQ)
    output v
      = hyloM (memoize (τUnroll (τPE φGen), ψTrail (w v))) (s, t, n)
instance Letable (PE ExpQ ExpQ) (PE ExpQ ExpQ) (PE ExpQ ExpQ) where
  mkVar name = τPE φGen (Var name)
  mkLet b h  = τPE φGen (Let b h)
  {-# INLINE mkVar #-}
  {-# INLINE mkLet #-}

shortestPathNF :: Int -> Int -> Int -> M.Matrix (Weight Int) -> ExpQ
shortestPathNF n s t mat = [| \ v -> $(unwrapPE (runSMemo (output [|v|])))|]
  where
    w  :: ExpQ -> Int -> Int -> Weight ExpQ
    w v i j = M.getElem i j mat <&> \idx -> [| $v V.! idx |]
    output :: ExpQ
           -> SMemo (PE ExpQ ExpQ) (Int, Int, Int) (PE ExpQ ExpQ) (PE ExpQ ExpQ)
    output v
      = let h = fmap (fmap (cata φGen))
              . fmap (cata (τPE In))
              . hyloM (memoize (τUnroll In, ψTrail (w v)))
        in h (s, t, n)
instance Letable
         (PE ExpQ ExpQ)
         (Fix (Term ExpQ (PE ExpQ ExpQ)))
         (PE ExpQ ExpQ) where
  mkVar v   = In (Var v)
  mkLet x h = τPE φGen (Let ((fmap (cata φGen) . cata (τPE In)) x) h)
  {-# INLINE mkVar #-}
  {-# INLINE mkLet #-}

unwrapPE :: PE ExpQ ExpQ -> ExpQ
unwrapPE e = case e of
  StInf    -> undefined
  DyAtom v -> v
  Dy x     -> x
{-# INLINE unwrapPE #-}

--
-- Counting
--

shortestPathC :: Int -> Int -> Int -> M.Matrix (Weight Int) -> Point
shortestPathC n s t mat = unwrapPE' (runSMemo output)
  where
    w  :: Int -> Int -> Weight ()
    w i j = void (M.getElem i j mat)
    output :: SMemo (PE Point Point) (Int, Int, Int) (PE Point Point) (PE Point Point)
    output = hyloM (memoize (τUnroll (τPE φCount), ψTrail w)) (s, t, n)
instance Letable (PE Point Point) (PE Point Point) (PE Point Point) where
  mkVar name = τPE φCount (Var name)
  mkLet b h  = τPE φCount (Let b h)
  {-# INLINE mkVar #-}
  {-# INLINE mkLet #-}

shortestPathCNF :: Int -> Int -> Int -> M.Matrix (Weight Int) -> Point
shortestPathCNF n s t mat = unwrapPE' (runSMemo output)
  where
    w  :: Int -> Int -> Weight ()
    w i j = void (M.getElem i j mat)
    output :: SMemo (PE Point Point) (Int, Int, Int) (PE Point Point) (PE Point Point)
    output =
      let h = fmap (fmap (cata φCount))
            . fmap (cata (τPE In))
            . hyloM (memoize (τUnroll In, ψTrail w))
      in h (s, t, n)
instance Letable
  (PE Point Point)
  (Fix (Term () (PE Point Point)))
  (PE Point Point) where
  mkVar v = In (Var v)
  mkLet x h = τPE φCount (Let ((fmap (cata φCount) . cata (τPE In)) x) h)
  {-# INLINE mkVar #-}
  {-# INLINE mkLet #-}
  
unwrapPE' :: PE Point Point -> Point
unwrapPE' e = case e of
  Dy x -> x
  _    -> mempty
{-# INLINE unwrapPE' #-}

flattenEdges :: M.Matrix Bool -> M.Matrix (Weight Int)
flattenEdges mat = scan mat & sequence & flip evalState 0
  where scan = M.mapPos $ \_ b ->
          if b then do idx <- get; modify succ; return (Wt idx)
          else return WInf
