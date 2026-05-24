
module LazyModuloInsertion where

import           Control.Monad
import           Control.Monad.State
import           Data.Array ((!))
import qualified Data.Array as A
import           Data.Bifunctor (second)
import           Data.Bits (shiftL)
import           Data.Function (fix, (&))
import           Data.Word
import           PrimRoots as Prim

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
  | LoAsr x Int | LoBitAnd x Int
  | LoAdd16 x x | LoSub16 x x
  | LoAdd32 x x | LoMul32 x x
  | LoSkip | LoLet IntType x (v -> x) | LoWrite Int x x
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

maxU18 :: Int
maxU18 = fromIntegral (1 `shiftL` 18 - 1 :: Word32)

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
       φ (LoLet U32 (φ (LoMul32 lo₁ lo₂))
          (\x ->
             φ (LoLet I16
                 (φ (LoSub16
                      (φ (LoI16 (mred (φ (LoVar x)))))
                      (φ (LoLit newHopeQ))))
                 (\v ->
                    φ (LoAdd16
                        (φ (LoVar v))
                        (φ (LoBitAnd (φ (LoAsr (φ (LoVar v)) 15))
                             newHopeQ)))))))
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
        in (φ (LoWrite i (φ (LoAdd16 lo₁ lo₂)) lo), undefined)
      else
        let σ' j | j == i = 2 | otherwise = σ j
            (lo, _) = evalCounter hi σ' ρ
        in (φ (LoLet U16 (φ (LoAdd16 lo₁ lo₂))
                (\x -> φ (LoWrite i (bred (φ (LoVar x))) lo))), undefined)
  HiSubW i hi₁ hi₂ hi ->
    let (lo₁, c₁) = evalCounter hi₁ σ ρ
        (lo₂, _)  = evalCounter hi₂ σ ρ in
      if θ i >= c₁ + 1 then
        let σ' j | j == i = c₁ + 1 | otherwise = σ j
            (lo, _) = evalCounter hi σ' ρ
        in (φ (LoWrite i
                (φ (LoSub16
                     (φ (LoAdd16 lo₁ (φ (LoLit newHopeQ))))
                     lo₂))
                 lo),
             undefined)
      else
        let σ' j | j == i = 2 | otherwise = σ j
            (lo, _) = evalCounter hi σ' ρ
        in (φ (LoLet U16 (φ (LoSub16
                           (φ (LoAdd16 lo₁ (φ (LoLit newHopeQ))))
                            lo₂))
               (\x -> φ (LoWrite i (bred (φ (LoVar x))) lo))), undefined)
  where
    bred x = let u = φ (φ (LoMul32 x (φ (LoLit 5))) `LoAsr` 16)
             in φ (x `LoSub16` φ (LoU16 (φ (LoMul32 u (φ (LoLit newHopeQ))))))
    mred x = let s = φ (x `LoBitAnd` maxU18)
                 r = φ (s `LoMul32` φ (LoLit newHopeQinv))
                 u = φ (r `LoBitAnd` maxU18)
               in φ (LoU16
                      (φ (φ (LoAdd32 x
                               (φ (LoMul32 u (φ (LoLit newHopeQ)))))
                            `LoAsr` 18)))

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

-- --
-- -- Generating C programs
-- --

type Name   = String
type Gensym = State (Int, [String])

gensym :: Gensym Name
gensym = do i <- gets fst; modify (\(j, s) -> (j + 1, s))
            return ("x" ++ show i)

statement :: String -> Gensym ()
statement s = modify (second (s :))

φGen :: LoTerm Name (Gensym String) -> Gensym String
φGen t = case t of
  LoLit i -> return (show i)
  LoRead n -> return ("A[" ++ show n ++ "]")
  LoVar v -> return v
  LoU16 x -> castM "uint16_t" x
  LoI16 x -> castM "int16_t" x
  LoAsr x n -> do s <- x; binop ">>" s (show n)
  LoBitAnd x n -> do s <- x; binop "&" s (show n)
  LoAdd16 x y -> binopM "+" x y
  LoSub16 x y -> binopM "-" x y
  LoAdd32 x y ->
    binopM "+" (castM "uint32_t" x) (castM "uint32_t" y)
  LoMul32 x y ->
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

-- Generator

hylo :: (Functor f) => (f b -> b, a -> f a) -> a -> b
hylo (φ, ψ) = fix (\f -> φ . fmap f . ψ)

newHopePrimRoots :: A.Array Int Int
newHopePrimRoots = Prim.primRootArray $ Prim.PRParam
  { Prim.n = 1024, Prim.q    = 12289
  , Prim.ω = 49, Prim.factor = 1 `shiftL` 16 }

newHopeNTT :: String
newHopeNTT =
  hylo (τUnroll (newHopePrimRoots!) (τInsert (const 4) φGen)
       , ψTrail 10) (1, 0, 0)
  & (\m -> evalCounter m (const 1) undefined)
  & fst & flip execState (0, []) & \(_, ss) ->
  reverse ss & map (\s -> "  " ++ s ++ ";\n") & join

outputNTT :: FilePath -> String -> IO ()
outputNTT path = writeFile path . wrapHeader . wrapFunc
  where wrapFunc s = "void ntt(uint16_t* A) {\n" ++ s ++ "}"
        wrapHeader = ("#include <stdint.h>\n\n" ++)
