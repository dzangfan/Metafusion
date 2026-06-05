{-# LANGUAGE CPP #-}
module LazyModuloInsertion where

import Control.Monad
import Control.Monad.State
import Data.Array ((!), Array)
import Data.Bifunctor (second)
import Data.Bits (shiftL, shiftR, (.&.))
import Data.Function ((&))
import Data.Functor
import Data.List.NonEmpty (NonEmpty(..))
import Data.Word
import GHC.Exts (inline)
import Prelude hiding (pred)
import PrimRoots as Prim
import Zoo

#ifdef TRACE
import Debug.Trace
#endif

data HiTerm v x
  = HiLit Int | HiRead Int | HiVar v | HiMul x x
  | HiSkip | HiLet x (v -> x)
  | HiAddW Int Int x x x | HiSubW Int Int x x x
  deriving Functor

data IntType = U32 | U16 | I16
instance Show IntType where
  show U32 = "uint32_t"
  show U16 = "uint16_t"
  show I16 = "int16_t"

data LoTerm v x
  = LoLit Int | LoRead Int | LoVar v
  | LoU16 x   | LoI16 x
  | LoAsr x Int | LoBitAnd x Int | LoMask x Int
  | LoAddU16 x x | LoSubU16 x x | LoSubI16 x x
  | LoAddU32 x x | LoMulU32 x x
  | LoSkip | LoLet IntType x (v -> x) | LoWrite Int x x
  | LoExact String x (v -> x)
  deriving Functor

--
-- Lazy Modulo Insertion
--

type St   = Int -> Int
type Ev v = Eq v => v -> Int
newtype Counter v x
  = Counter { evalCounter :: St -> Ev v -> (x, Int) }
  deriving Functor

type Threshold = Int -> Int

newHopeQ :: Int
newHopeQ = 12289

newHopeQinv :: Int
newHopeQinv = 12287

undef :: Int
undef = 0

τInsert :: forall v. Eq v => Threshold ->
  forall x. (LoTerm v x -> x)
  -> HiTerm v (Counter v x)
  -> Counter v x
τInsert θ φ t = Counter $ \σ ρ -> case t of
  HiLit n  -> (inline φ (LoLit n), undef)
  HiRead i -> (inline φ (LoRead i), σ i)
  HiVar v  -> (inline φ (LoVar v), ρ v)
  HiMul hi₁ hi₂ ->
    let (lo₁, _) = evalCounter hi₁ σ ρ
        (lo₂, _) = evalCounter hi₂ σ ρ
    in (,undef) $
       inline φ (LoLet U32 (inline φ (LoMulU32 lo₁ lo₂))
          (\x -> exact φ "MRED" (csub φ) (mred φ (inline φ (LoVar x)))))
  HiSkip -> (inline φ LoSkip, undef)
  HiLet hi h ->
    let (lo, c) = evalCounter hi σ ρ
        ρ' u v | u == v = c | otherwise = ρ v
        h' v = evalCounter (h v) σ (ρ' v) & fst
    in (inline φ (LoLet U16 lo h'), undef)
  HiAddW _ i hi₁ hi₂ hi ->
    let (lo₁, c₁) = evalCounter hi₁ σ ρ
        (lo₂, _)  = evalCounter hi₂ σ ρ in
      if θ i >= c₁ + 1 then
        let σ' j | j == i = c₁ + 1 | otherwise = σ j
            (lo, _) = evalCounter hi σ' ρ
        in (inline φ (LoWrite i (inline φ (LoAddU16 lo₁ lo₂)) lo), undef)
      else
        let σ' j | j == i = 1 | otherwise = σ j
            (lo, _) = evalCounter hi σ' ρ
        in (inline φ (LoLet U16 (inline φ (LoAddU16 lo₁ lo₂))
                (\x ->
                   inline φ (LoWrite i
                               (exact φ "BRED" (bred φ) (inline φ (LoVar x))) lo))),
             undef)
  HiSubW _ i hi₁ hi₂ hi ->
    let (lo₁, c₁) = evalCounter hi₁ σ ρ
        (lo₂, _)  = evalCounter hi₂ σ ρ in
      if θ i >= c₁ + 1 then
        let σ' j | j == i = c₁ + 1 | otherwise = σ j
            (lo, _) = evalCounter hi σ' ρ
        in (inline φ (LoWrite i
                        (inline φ (LoSubU16
                            (inline φ (LoAddU16 lo₁ (inline φ (LoLit newHopeQ))))
                     lo₂))
                 lo),
             undef)
      else
        let σ' j | j == i = 1 | otherwise = σ j
            (lo, _) = evalCounter hi σ' ρ
        in (inline φ
            (LoLet U16
             (inline φ (LoSubU16
                          (inline φ (LoAddU16 lo₁ (inline φ (LoLit newHopeQ))))
                          lo₂))
                (\x -> inline φ (LoWrite i (exact φ "BRED" (bred φ) (inline φ (LoVar x))) lo))),
             undef)
{-# INLINE τInsert #-}

exact :: forall v x. (LoTerm v x -> x) -> String -> (x -> x) -> x -> x
exact φ s f x = inline φ (LoExact s x (\v -> f (inline φ (LoVar v))))
{-# INLINE exact #-}

bred :: forall v x. (LoTerm v x -> x) -> x -> x
bred φ x =
  let u = inline φ (inline φ (LoMulU32 x (inline φ (LoLit 5))) `LoAsr` 16)
  in inline φ (x `LoSubU16` inline φ (LoU16 (inline φ (LoMulU32 u (inline φ (LoLit newHopeQ))))))
{-# INLINE bred #-}

mred :: forall v x. (LoTerm v x -> x) -> x -> x
mred φ x =
  let s = inline φ (x `LoMask` 16)
      r = inline φ (s `LoMulU32` inline φ (LoLit newHopeQinv))
      u = inline φ (r `LoMask` 16)
  in inline φ (LoU16 (inline φ (inline φ (LoAddU32 x (inline φ (LoMulU32 u (inline φ (LoLit newHopeQ)))))
                    `LoAsr` 16)))
{-# INLINE mred #-}

csub :: forall v x. (LoTerm v x -> x) -> x -> x
csub φ x =
  inline φ (LoLet I16
       (inline φ (LoSubI16 (inline φ (LoI16 x)) (inline φ (LoLit newHopeQ))))
       (\v ->
           inline φ (LoAddU16
                (inline φ (LoVar v))
                (inline φ (LoBitAnd (inline φ (LoAsr (inline φ (LoVar v)) 15)) newHopeQ)))))
{-# INLINE csub #-}

--
-- Generating NTT trail
--

data Trail a x = TrHalt | TrNode a x deriving Functor

ψTrail :: Int -> Int -> (Int, Int, Int) -> Trail (Int, Int, Int) (Int, Int, Int)
ψTrail n logN (s, k, j)
  | s <= logN && k <= n - 1 && j <= o = TrNode (s, k, j) (s, k, j + 1)
  | s <= logN && k <= n - 1           = ψTrail n logN (s, k + m, 0)
  | s <= logN                         = ψTrail n logN (s + 1, 0, 0)
  | otherwise                         = TrHalt
  where m = 2 ^ s
        o = 2 ^ (s - 1) - 1

--
-- Generating a modulo-free, unrolled NTT program from the trail
--

type Ω = Int -> Int

τUnroll :: Ω -> forall v x. (HiTerm v x -> x)
  -> Trail (Int, Int, Int) x -> x
τUnroll getΩ φ trail = case trail of
  TrHalt -> inline φ HiSkip
  TrNode (s, k, j) x ->
    let m = 2 ^ s; o = 2 ^ (s - 1) - 1 in
      inline φ (HiLet (inline φ (HiRead (k + j)))
          (\u ->
              inline φ (HiLet (inline φ (HiMul
                        (inline φ (HiRead (k + j + m `div` 2)))
                        (inline φ (HiLit (getΩ (o + j))))))
               (\t ->
                  inline φ (HiAddW s (k + j) (inline φ (HiVar u)) (inline φ (HiVar t))
                      (inline φ (HiSubW s (k + j + m `div` 2) (inline φ (HiVar u)) (inline φ (HiVar t))
                           x)))))))
{-# INLINE τUnroll #-}

--
-- Generating C programs
--

type Name   = String
type Gensym = State (Int, [String])

gensym :: Gensym Name
gensym = do i <- gets fst; modify (\(j, s) -> (j + 1, s))
            return ("x" ++ show i)

statement :: String -> Gensym ()
statement s = modify (second (s :))

maxUint :: Int -> Integer
maxUint n = fromIntegral (1 `shiftL` n - 1 :: Word32)

φGen :: LoTerm Name (Gensym String) -> Gensym String
φGen t = case t of
  LoLit i -> return (show i)
  LoRead n -> return ("A[" ++ show n ++ "]")
  LoVar v -> return v
  LoU16 x -> castM "uint16_t" x
  LoI16 x -> castM "int16_t" x
  LoAsr x n -> do s <- x; binop ">>" s (show n)
  LoBitAnd x n -> do s <- x; binop "&" s (show n)
  LoMask x n -> do
    s <- x
    return ("(" ++ s ++ " & " ++ show (maxUint n) ++ ")")
  LoAddU16 x y -> binopM "+" x y
  LoSubU16 x y -> binopM "-" x y
  LoSubI16 x y -> binopM "-" x y
  LoAddU32 x y ->
    binopM "+" (castM "uint32_t" x) (castM "uint32_t" y)
  LoMulU32 x y ->
    binopM "*" (castM "uint32_t" x) (castM "uint32_t" y)
  LoSkip -> return "";
  LoLet it x h -> do
    res <- x; name <- gensym
    statement (show it ++ " " ++ name ++ " = " ++ res)
    h name
  LoWrite n x body -> do
    res <- x
    statement ("A[" ++ show n ++ "] = " ++ res)
    body
  LoExact op x h ->
    x >>= h <&> (\s -> tag ++ s ++ tag) where tag = "/* " ++ op ++ " */"
  where binop :: Monad m => String -> String -> String -> m String
        binop op a b =
          return ("(" ++ a ++ " " ++ op ++ " " ++ b ++  ")")
        binopM :: Monad m
               => String -> m String -> m String -> m String
        binopM op m₁ m₂ = do s₁ <- m₁; s₂ <- m₂; binop op s₁ s₂
        cast :: String -> String -> String
        cast ty s = "((" ++ ty ++ ")" ++ s ++ ")"
        castM :: Monad m => String -> m String -> m String
        castM ty = fmap (cast ty)

--
-- Interval analysis
--

type Iv = (Integer, Integer)
type StIv = Int -> Iv
type EvIv = Integer -> Iv
data StoreIv = StoreIv { varPool :: Integer, lino :: Int, focus :: (Int, Int) }
  deriving Show
type StateIv = StateT StoreIv (Either (String, Int))
newtype IA = IA { evalIA :: StIv -> EvIv -> StateIv Iv }

(⊆) :: Iv -> Iv -> Bool
(x₁, y₁) ⊆ (x₂, y₂) = x₂ <= x₁ && y₁ <= y₂
{-# INLINE (⊆) #-}

gensymIA :: StateIv Integer
gensymIA = do i <- gets varPool
              modify (\s -> s { varPool = varPool s + 1 })
              return i

assertI :: String -> Iv -> Iv -> StateIv ()
assertI op i j
  -- | i ⊆ j = trace (op ++ ": " ++ show i ++ " ⊆ " ++ show j) (return ())
  | i ⊆ j = return ()
  | otherwise = do f <- gets (fst . focus);
                   lift (Left (op ++ ": " ++ show i ++ " ⊈ " ++ show j, f))

cache :: Int -> StateIv ()
cache i = do (_, i1) <- gets focus; modify (\s -> s { focus = (i1, i) })

maxU16 :: Integer
maxU16 = 65535

ivU16 :: Iv
ivU16 = (0, 65535)

ivI16 :: Iv
ivI16 = (-32768, 32767)

ivU32 :: Iv
ivU32 = (0, 4294967295)

φIA :: LoTerm Integer IA -> IA
φIA t = IA $ \σ ρ -> case t of
  LoLit n -> return (m, m) where m = fromIntegral n
  LoRead i -> do cache i; return (σ i)
  LoVar v  -> return (ρ v)
  LoU16 x -> do iv <- evalIA x σ ρ
                return (if iv ⊆ ivU16 then iv else ivU16)
  LoI16 x -> do iv <- evalIA x σ ρ
                assertI "LoI16" iv ivI16
                return iv
  LoAsr x n -> do (a, b) <- evalIA x σ ρ; return (a `asr` n, b `asr` n)
  LoBitAnd x n -> exactInterv (`bitAnd` fromIntegral n) <$> evalIA x σ ρ
  LoMask x n -> do iv <- evalIA x σ ρ
                   let bounds = (0, maxUint n)
                   return (if iv ⊆ bounds then iv else bounds)
  LoAddU16 a b -> do iv <- liftM2 (+♯) (evalIA a σ ρ) (evalIA b σ ρ)
                     assertI "LoAddU16" iv ivU16
                     return iv
  LoSubU16 a b -> do iv <- liftM2 (-♯) (evalIA a σ ρ) (evalIA b σ ρ)
                     assertI "LoSubU16" iv ivU16
                     return iv
  LoSubI16 a b -> do iv <- liftM2 (-♯) (evalIA a σ ρ) (evalIA b σ ρ)
                     assertI "LoSubI16" iv ivI16
                     return iv
  LoAddU32 a b -> do iv <- liftM2 (+♯) (evalIA a σ ρ) (evalIA b σ ρ)
                     assertI "LoAddU32" iv ivU32
                     return iv
  LoMulU32 a b -> do iv <- liftM2 (×♯) (evalIA a σ ρ) (evalIA b σ ρ)
                     assertI "LoMulU32" iv ivU32
                     return iv
  LoSkip -> return (0, 0)
  LoLet it x h -> do iv <- evalIA x σ ρ
                     let bounds =
                           case it of U32 -> ivU32; U16 -> ivU16; I16 -> ivI16
                     assertI "LoLet" iv bounds
                     name <- gensymIA
                     let ρ' v | v == name = iv | otherwise = ρ v
                     evalIA (h name) σ ρ'
  LoWrite i x h -> do iv <- evalIA x σ ρ
                      assertI "LoWrite" iv ivU16
#ifdef TRACE
                      l <- gets lino
                      trace ("\ESC[1A\ESC[2K" ++ show l)
                        (return ())
                      modify (\s -> s { lino = l + 1 })
#endif
                      let σ' j | i == j = iv | otherwise = σ j
                      evalIA h σ' ρ
  LoExact _ x h -> do (a, b) <- evalIA x σ ρ
                      ivs <- sequence (run a :| [ run z | z <- [a + 1 .. b]])
                      return (minmax (fst <$> ivs))
                        where run n = do name <- gensymIA
                                         let ρ' v
                                               | v == name = (n, n)
                                               | otherwise = ρ v
                                         evalIA (h name) σ ρ'
  where (+♯) :: Iv -> Iv -> Iv
        (-♯) :: Iv -> Iv -> Iv
        (×♯) :: Iv -> Iv -> Iv
        (x₁, y₁) +♯ (x₂, y₂) = (x₁ + x₂, y₁ + y₂)
        (x₁, y₁) -♯ (x₂, y₂) = (x₁ - y₂, y₁ - x₂)
        (x₁, y₁) ×♯ (x₂, y₂) = (minimum a, maximum a)
          where a = [ x₁ * x₂, x₁ * y₂, y₁ * x₂, y₁ * y₂]
        {-# INLINE (+♯) #-}
        {-# INLINE (-♯) #-}
        {-# INLINE (×♯) #-}
{-# INLINE φIA #-}

bitAnd :: Integer -> Integer -> Integer
bitAnd = withWord32 (.&.)

asr :: Integer -> Int -> Integer
asr a b = fromIntegral (fromIntegral a `shiftR` b :: Word32)

withWord32 :: (Word32 -> Word32 -> Word32) -> Integer -> Integer -> Integer
withWord32 (⊕) a b = fromIntegral (fromIntegral a ⊕ fromIntegral b)

exactInterv :: (Integer -> Integer) -> Iv -> Iv
exactInterv g (lo, hi) = let glo = g lo in exactRng glo glo (lo + 1)
  where exactRng mi ma i
          | i > hi = (mi, ma)
          | otherwise =
          let j = g i
              !mi' = min j mi
              !ma' = max j ma
          in exactRng mi' ma' (i + 1)

minmax :: Ord a => NonEmpty a -> (a, a)
minmax (hd :| tl) = exactRng hd hd tl
  where exactRng mi ma [] = (mi, ma)
        exactRng mi ma (x:xs) =
          let !mi' = min x mi
              !ma' = max x ma
          in exactRng mi' ma' xs

--
-- Couting modulos
--

newtype Point = Point (Int, Int) deriving Show

instance Semigroup Point where
  Point (a, b) <> Point (c, d) = Point (a + c, b + d)
instance Monoid Point where mempty = Point (0, 0)

type Modulos = State Int Point

gensymModulos :: State Int Int
gensymModulos = do i <- get; modify succ; return i

φModulos :: LoTerm Int Modulos -> Modulos
φModulos t = case t of
  LoLit _  -> return mempty
  LoRead _ -> return mempty
  LoVar _  -> return mempty
  LoU16 x      -> x
  LoI16 x      -> x
  LoAsr x _    -> x
  LoBitAnd x _ -> x
  LoMask x _   -> x
  LoAddU16 a b -> liftM2 (<>) a b
  LoSubU16 a b -> liftM2 (<>) a b
  LoSubI16 a b -> liftM2 (<>) a b
  LoAddU32 a b -> liftM2 (<>) a b
  LoMulU32 a b -> liftM2 (<>) a b
  LoSkip -> return mempty
  LoLet _ x h -> do i <- gensymModulos; liftM2 (<>) x (h i)
  LoWrite _ a b -> liftM2 (<>) a b
  LoExact "BRED" x h -> do
    i <- gensymModulos
    m <- liftM2 (<>) x (h i)
    return (m <> Point (1, 0))
  LoExact "MRED" x h -> do
    i <- gensymModulos
    m <- liftM2 (<>) x (h i)
    return (m <> Point (0, 1))
  LoExact _ x h -> do i <- gensymModulos; liftM2 (<>) x (h i)
            
--
-- Generator
--

safeThreshold :: Threshold
safeThreshold = const 4

newHopePrimRoots :: Array Int Int
newHopePrimRoots = Prim.primRootArray $ Prim.PRParam
  { Prim.n = 1024, Prim.q    = 12289
  , Prim.ω = 49, Prim.factor = 1 `shiftL` 16 }

newHopeNTT :: Threshold -> String
newHopeNTT θ =
  hylo ( τUnroll (newHopePrimRoots!) (τInsert θ φGen)
       , ψTrail 1024 10) (1, 0, 0)
  & (\m -> evalCounter m (const 1) (const undef))
  & fst & flip execState (0, []) & \(_, ss) ->
  reverse ss & map (\s -> "  " ++ s ++ ";\n") & join

newHopeNTTNF :: Threshold -> String
newHopeNTTNF θ =
  h (1, 0, 0)
  & (\m -> evalCounter m (const 1) (const undef))
  & fst & flip execState (0, []) & \(_, ss) ->
  reverse ss & map (\s -> "  " ++ s ++ ";\n") & join
  where h = fmap (cata φGen)
          . cata (τInsert θ In)
          . cata (τUnroll (newHopePrimRoots!) In)
          . ana (ψTrail 1024 10)

outputNTT :: FilePath -> [String] -> String -> IO ()
outputNTT path header = writeFile path . wrapHeader . wrapFunc
  where wrapFunc s = "void ntt(uint16_t* A) {\n  bit_reverse(A);\n" ++ s ++ "}"
        wrapHeader = (header' ++)
        header' = header
          & map ("// " ++)
          & (++ ["\n#include <stdint.h>\n", "void bit_reverse(uint16_t*);\n"])
          & unlines

--
-- Analysis
--

newHopeVerif :: Threshold -> Either (String, Int) (Iv, StoreIv)
newHopeVerif θ =
  hylo ( τUnroll (newHopePrimRoots!) (τInsert θ φIA)
       , ψTrail 1024 10) (1, 0, 0)
  & (\m -> evalCounter m (const 1) (const undef))
  & (\(m, _) -> evalIA m (const (0, fromIntegral newHopeQ - 1)) (\_ -> undefined))
  & flip runStateT (StoreIv { varPool = 0, lino = 1, focus = (0, 0) })

newHopeVerifNF :: Threshold -> Either (String, Int) (Iv, StoreIv)
newHopeVerifNF θ = h (1, 0, 0)
  & (\m -> evalCounter m (const 1) (const undef))
  & (\(m, _) -> evalIA m (const (0, fromIntegral newHopeQ - 1)) (\_ -> undefined))
  & flip runStateT (StoreIv { varPool = 0, lino = 1, focus = (0, 0) })
  where h = fmap (cata φIA)
          . cata (τInsert θ In)
          . cata (τUnroll (newHopePrimRoots!) In)
          . ana (ψTrail 1024 10)

--
-- Counting
--

newHopeModulos :: Threshold -> Point
newHopeModulos θ =
  hylo ( τUnroll (newHopePrimRoots!) (τInsert θ φModulos)
       , ψTrail 1024 10) (1, 0, 0)
  & (\m -> evalCounter m (const 1) (const undef))
  & (\(m, _) -> evalState m 0)

newHopeModulosNF :: Threshold -> Point
newHopeModulosNF θ =
  h (1, 0, 0)
  & (\m -> evalCounter m (const 1) (const undef))
  & (\(m, _) -> evalState m 0)
  where h = fmap (cata φModulos)
          . cata (τInsert θ In)
          . cata (τUnroll (newHopePrimRoots!) In)
          . ana (ψTrail 1024 10)

φTrailToList :: Trail (Int, Int, Int) [(Int, Int, Int)] -> [(Int, Int, Int)]
φTrailToList tr = case tr of TrHalt -> []; TrNode h t -> h:t

masudaModulos :: Point
masudaModulos =
  let trail   = hylo (φTrailToList, ψTrail 1024 10) (1, 0, 0)
      mredN    = length trail
      bredSubN = length trail
      bredAddN = filter (\(s, _, _) -> s `elem` [3, 6, 9]) trail & length
  in Point (bredAddN + bredSubN, mredN)

--
-- A noval lazy reduction scheme
--

τHandmade :: forall v x. (LoTerm v x -> x) -> HiTerm v x -> x
τHandmade φ e = case e of
  HiLit  n -> inline φ (LoLit n)
  HiRead i -> inline φ (LoRead i)
  HiVar  v -> inline φ (LoVar v)
  HiMul a b -> inline φ (LoLet U32 (inline φ (LoMulU32 a b))
                   (\x -> exact φ "MRED" (csub φ) (mred φ (inline φ (LoVar x)))))
  HiSkip -> inline φ LoSkip
  HiLet x h -> inline φ (LoLet U16 x h)
  HiAddW s i u t h
    | pred s i ->
      inline φ (LoLet U16 (inline φ (LoAddU16 u t))
           (\x ->
               inline φ (LoWrite i
                    (exact φ "BRED" (bred φ) (inline φ (LoVar x))) h)))
    | otherwise ->
      inline φ (LoWrite i (inline φ (LoAddU16 u t)) h)
  HiSubW s i u t h
    | pred s i ->
      inline φ (LoLet U16
           (inline φ (LoSubU16 (inline φ (LoAddU16 u (inline φ (LoLit newHopeQ)))) t))
           (\x -> inline φ (LoWrite i (exact φ "BRED" (bred φ) (inline φ (LoVar x))) h)))
    | otherwise ->
      inline φ (LoWrite i (inline φ (LoSubU16 (inline φ (LoAddU16 u (inline φ (LoLit newHopeQ)))) t)) h)
  where pred :: Int -> Int -> Bool
        pred s i = (s `mod` 4 == 0) && (i `mod` (2 ^ (s + 1)) < 2 ^ s)
{-# INLINE τHandmade #-}

handmadeNTT :: String
handmadeNTT =
  hylo ( τUnroll (newHopePrimRoots!) (τHandmade φGen)
       , ψTrail 1024 10) (1, 0, 0)
  & flip execState (0, []) & \(_, ss) ->
  reverse ss & map (\s -> "  " ++ s ++ ";\n") & join

handmadeVerif :: Either (String, Int) (Iv, StoreIv)
handmadeVerif =
  hylo ( τUnroll (newHopePrimRoots!) (τHandmade φIA)
       , ψTrail 1024 10) (1, 0, 0)
  & (\m -> evalIA m (const (0, fromIntegral newHopeQ - 1)) (\_ -> undefined))
  & flip runStateT (StoreIv { varPool = 0, lino = 1, focus = (0, 0) })

handmadeModulos :: Point
handmadeModulos =
  hylo ( τUnroll (newHopePrimRoots!) (τHandmade φModulos)
       , ψTrail 1024 10) (1, 0, 0)
  & flip evalState 0
