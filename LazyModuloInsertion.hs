
module LazyModuloInsertion where

import Control.Monad
import Control.Monad.State
import Data.Array ((!), Array)
import Data.Bifunctor (first, second)
import Data.Bits (shiftL, shiftR, (.&.))
import Data.Function (fix, (&))
import Data.Functor
import Data.List.NonEmpty (NonEmpty(..))
import Data.Word
import Debug.Trace
import PrimRoots as Prim

data HiTerm v x
  = HiLit Int | HiRead Int | HiVar v | HiMul x x
  | HiSkip | HiLet x (v -> x)
  | HiAddW Int x x x | HiSubW Int x x x
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

τInsert :: forall v. Eq v => Threshold ->
  forall x. (LoTerm v x -> x)
  -> HiTerm v (Counter v x)
  -> Counter v x
τInsert θ φ t = Counter $ \σ ρ -> case t of
  HiLit n  -> (φ (LoLit n), undefined)
  HiRead i -> (φ (LoRead i), σ i)
  HiVar v  -> (φ (LoVar v), ρ v)
  HiMul hi₁ hi₂ ->
    let (lo₁, _) = evalCounter hi₁ σ ρ
        (lo₂, _) = evalCounter hi₂ σ ρ
    in (,undefined) $
       φ (LoLet U32 (φ (LoMulU32 lo₁ lo₂))
          (\x -> exact "MRED" csub (mred (φ (LoVar x)))))
  HiSkip -> (φ LoSkip, undefined)
  HiLet hi h ->
    let (lo, c) = evalCounter hi σ ρ
        ρ' u v | u == v = c | otherwise = ρ v
        h' v = evalCounter (h v) σ (ρ' v) & fst
    in (φ (LoLet U16 lo h'), undefined)
  HiAddW i hi₁ hi₂ hi ->
    let (lo₁, c₁) = evalCounter hi₁ σ ρ
        (lo₂, _)  = evalCounter hi₂ σ ρ in
      if θ i >= c₁ + 1 then
        let σ' j | j == i = c₁ + 1 | otherwise = σ j
            (lo, _) = evalCounter hi σ' ρ
        in (φ (LoWrite i (φ (LoAddU16 lo₁ lo₂)) lo), undefined)
      else
        let σ' j | j == i = 2 | otherwise = σ j
            (lo, _) = evalCounter hi σ' ρ
        in (φ (LoLet U16 (φ (LoAddU16 lo₁ lo₂))
                (\x -> φ (LoWrite i
                           (exact "BRED" bred (φ (LoVar x))) lo))), undefined)
  HiSubW i hi₁ hi₂ hi ->
    let (lo₁, c₁) = evalCounter hi₁ σ ρ
        (lo₂, _)  = evalCounter hi₂ σ ρ in
      if θ i >= c₁ + 1 then
        let σ' j | j == i = c₁ + 1 | otherwise = σ j
            (lo, _) = evalCounter hi σ' ρ
        in (φ (LoWrite i
                (φ (LoSubU16
                     (φ (LoAddU16 lo₁ (φ (LoLit newHopeQ))))
                     lo₂))
                 lo),
             undefined)
      else
        let σ' j | j == i = 2 | otherwise = σ j
            (lo, _) = evalCounter hi σ' ρ
        in (φ (LoLet U16 (φ (LoSubU16
                           (φ (LoAddU16 lo₁ (φ (LoLit newHopeQ))))
                            lo₂))
                (\x -> φ (LoWrite i (exact "BRED" bred (φ (LoVar x))) lo))),
             undefined)
  where
    exact s f x = φ (LoExact s x (f . φ . LoVar))
    bred x = let u = φ (φ (LoMulU32 x (φ (LoLit 5))) `LoAsr` 16)
             in φ (x `LoSubU16` φ (LoU16 (φ (LoMulU32 u (φ (LoLit newHopeQ))))))
    mred x = let s = φ (x `LoMask` 16)
                 r = φ (s `LoMulU32` φ (LoLit newHopeQinv))
                 u = φ (r `LoMask` 16)
               in φ (LoU16
                      (φ (φ (LoAddU32 x
                               (φ (LoMulU32 u (φ (LoLit newHopeQ)))))
                            `LoAsr` 16)))
    csub x = φ (LoLet I16
                 (φ (LoSubI16 (φ (LoI16 x)) (φ (LoLit newHopeQ))))
                 (\v ->
                    φ (LoAddU16
                        (φ (LoVar v))
                        (φ (LoBitAnd (φ (LoAsr (φ (LoVar v)) 15))
                             newHopeQ)))))

-- --
-- -- Lazy Modulo Insertion
-- --

-- type Iv   = (Int, Int)
-- type St   = Int -> Iv
-- type Ev v = Eq v => v -> Iv
-- newtype Ins v x
--   = Ins { evalIns :: St -> Ev v -> (x, Iv) }
--   deriving Functor

-- τInsert :: forall v. Eq v => Param
--   ->  forall x. (Term v x -> x)
--   -> Term v (Ins v x)
--   -> Ins v x
-- τInsert p φ t = Ins $ \σ ρ -> case t of
--   TLit  n -> (φ (TLit n), (n, n)) ↓ (0, getINTMAX₁ p)
--   TRead i -> (φ (TRead i), σ i)
--   TVar  v -> (φ (TVar v),  ρ v)
--   TModQ e -> evalIns e σ ρ ↓ (0, getQ p - 1)
--   TAdd e₁ e₂ ->
--     let (r₁, iv₁) = evalIns e₁ σ ρ
--         (r₂, iv₂) = evalIns e₂ σ ρ
--     in DT.traceShow (σ 0) (φ (TAdd r₁ r₂), iv₁ +♯ iv₂) ↓ (0, getINTMAX₁ p)
--   TSub e₁ e₂ ->
--     let (r₁, iv₁) = evalIns e₁ σ ρ
--         (r₂, iv₂) = evalIns e₂ σ ρ
--     in (φ (TSub r₁ r₂), iv₁ -♯ iv₂)
--        ↓ (0, getINTMAX₁ p)
--   TMul e₁ e₂ ->
--     let (r₁, iv₁) = evalIns e₁ σ ρ
--         (r₂, iv₂) = evalIns e₂ σ ρ
--     in (φ (TMul r₁ r₂), iv₁ ×♯ iv₂) ↓ (0, getINTMAX₁ p)
--   TSkip -> (φ TSkip, undefined)
--   TLet e h ->
--     let (r, iv) = evalIns e σ ρ ↓ (0, getINTMAX₂ p)
--         h' v    = fst $ evalIns (h v) σ ρ'
--           where ρ' w | w == v = iv | otherwise = ρ w
--     in (φ (TLet r h'), undefined)
--   TWrite i e s ->
--     let (r, iv) = evalIns e σ ρ ↓ (0, getINTMAX₃ p)
--         (s', _) = evalIns s σ' ρ
--           where  σ' j | i == j = iv | otherwise = σ j
--     in (φ (TWrite i r s'), undefined)
--   where (⊆) :: Iv -> Iv -> Bool
--         (+♯) :: Iv -> Iv -> Iv
--         (-♯) :: Iv -> Iv -> Iv
--         (×♯) :: Iv -> Iv -> Iv
--         (e, iv₁) ↓ iv₂
--           | iv₁ ⊆ iv₂ = (e, iv₁)
--           | otherwise = (φ (TModQ e), (0, q - 1))
--           where q = getQ p
--         (x₁, y₁) ⊆ (x₂, y₂) = x₂ <= x₁ && y₁ <= y₂
--         (x₁, y₁) +♯ (x₂, y₂) = (x₁ + x₂, y₁ + y₂)
--         (x₁, y₁) -♯ (x₂, y₂) = (x₁ - y₂, y₁ - x₂)
--         (x₁, y₁) ×♯ (x₂, y₂) = (minimum a, maximum a)
--           where a = [ x₁ * x₂, x₁ * y₂, y₁ * x₂, y₁ * y₂]

--
-- Generating NTT trail
--

data Trail a x = TrHalt | TrNode a x deriving Functor

ψTrail :: Int -> (Int, Int, Int) -> Trail (Int, Int, Int) (Int, Int, Int)
ψTrail logN (s, k, j)
  | s <= logN && k <= m - 1 && j <= o = TrNode (s, k, j) (s, k, j + 1)
  | s <= logN && k <= m - 1           = ψTrail logN (s, k + m, 0)
  | s <= logN                         = ψTrail logN (s + 1, 0, 0)
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
  TrHalt -> φ HiSkip
  TrNode (s, k, j) x ->
    let m = 2 ^ s; o = 2 ^ (s - 1) - 1 in
      φ (HiLet (φ (HiRead (k + j)))
          (\u ->
          φ (HiLet (φ (HiMul
                        (φ (HiRead (k + j + m `div` 2)))
                        (φ (HiLit (getΩ (o + j))))))
               (\t ->
                  φ (HiAddW (k + j) (φ (HiVar u)) (φ (HiVar t))
                      (φ (HiSubW (k + j + m `div` 2) (φ (HiVar u)) (φ (HiVar t))
                           x)))))))

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
newtype IA = IA { evalIA :: StIv -> EvIv
                  -> StateT (Integer, Int) (Either String) Iv }

(⊆) :: Iv -> Iv -> Bool
(x₁, y₁) ⊆ (x₂, y₂) = x₂ <= x₁ && y₁ <= y₂

gensymIA :: StateT (Integer, Int) (Either String) Integer
gensymIA = do i <- gets fst; modify (first succ); return i

assertI :: String -> Iv -> Iv -> StateT (Integer, Int) (Either String) ()
assertI op i j
  -- | i ⊆ j = trace (op ++ ": " ++ show i ++ " ⊆ " ++ show j) (return ())
  | i ⊆ j = return ()
  | otherwise = lift (Left (op ++ ": " ++ show i ++ " ⊈ " ++ show j))

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
  LoRead i -> return (σ i)
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
                      lino <- gets snd
                      traceShow lino (return ())
                      modify (second succ)
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

bitAnd :: Integer -> Integer -> Integer
bitAnd = withWord32 (.&.)

asr :: Integer -> Int -> Integer
asr a b = fromIntegral (fromIntegral a `shiftR` b :: Word32)

withWord32 :: (Word32 -> Word32 -> Word32) -> Integer -> Integer -> Integer
withWord32 (⊕) a b = fromIntegral (fromIntegral a ⊕ fromIntegral b)

exactInterv :: (Integer -> Integer) -> Iv -> Iv
exactInterv g (lo, hi) = let glo = g lo in exact glo glo (lo + 1)
  where exact mi ma i
          | i > hi = (mi, ma)
          | otherwise =
          let j = g i
              !mi' = min j mi
              !ma' = max j ma
          in exact mi' ma' (i + 1)

minmax :: Ord a => NonEmpty a -> (a, a)
minmax (hd :| tl) = exact hd hd tl
  where exact mi ma [] = (mi, ma)
        exact mi ma (x:xs) =
          let !mi' = min x mi
              !ma' = max x ma
          in exact mi' ma' xs

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

hylo :: (Functor f) => (f b -> b, a -> f a) -> a -> b
hylo (φ, ψ) = fix (\f -> φ . fmap f . ψ)

newHopePrimRoots :: Array Int Int
newHopePrimRoots = Prim.primRootArray $ Prim.PRParam
  { Prim.n = 1024, Prim.q    = 12289
  , Prim.ω = 49, Prim.factor = 1 `shiftL` 16 }

newHopeNTT :: String
newHopeNTT =
  hylo ( τUnroll (newHopePrimRoots!) (τInsert (const 4) φGen)
       , ψTrail 10) (1, 0, 0)
  & (\m -> evalCounter m (const 1) undefined)
  & fst & flip execState (0, []) & \(_, ss) ->
  reverse ss & map (\s -> "  " ++ s ++ ";\n") & join

outputNTT :: FilePath -> String -> IO ()
outputNTT path = writeFile path . wrapHeader . wrapFunc
  where wrapFunc s = "void ntt(uint16_t* A) {\n  bit_reverse(A);\n" ++ s ++ "}"
        wrapHeader =
          ("#include <stdint.h>\n\nvoid bit_reverse(uint16_t*);\n\n" ++)

--
-- Analysis
--

newHopeVerif :: Either String (Iv, (Integer, Int))
newHopeVerif =
  hylo ( τUnroll (newHopePrimRoots!) (τInsert (const 4) φIA)
       , ψTrail 10) (1, 0, 0)
  & (\m -> evalCounter m (const 1) undefined)
  & (\(m, _) -> evalIA m (const (0, fromIntegral newHopeQ - 1)) undefined)
  & flip runStateT (0, 1)

--
-- Counting
--

newHopeModulos :: Point
newHopeModulos =
  hylo ( τUnroll (newHopePrimRoots!) (τInsert (const 4) φModulos)
       , ψTrail 10) (1, 0, 0)
  & (\m -> evalCounter m (const 1) undefined)
  & (\(m, _) -> evalState m 0)

φTrailToList :: Trail (Int, Int, Int) [(Int, Int, Int)] -> [(Int, Int, Int)]
φTrailToList tr = case tr of TrHalt -> []; TrNode h t -> h:t

masudaModulos :: Point
masudaModulos =
  let trail   = hylo (φTrailToList, ψTrail 10) (1, 0, 0)
      mred    = length trail
      bredSub = length trail
      bredAdd = filter (\(s, _, _) -> s `elem` [3, 6, 9]) trail & length
  in Point (bredAdd + bredSub, mred)
