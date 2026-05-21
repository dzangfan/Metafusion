
module LazyModuloInsertion where

import           Control.Monad (liftM2)
import           Control.Monad.State
import           Data.Array ((!))
import qualified Data.Array as A
import           Data.Bits (shiftL)
import           Data.Function (fix, (&))
import           Data.Functor ((<&>))
import           Data.Word
import           Debug.Trace as DT
import           PrimRoots as Prim

data Term v x
  = TLit Int | TRead Int | TVar v
  | TModQ x | TAdd x x | TSub x x | TMul x x
  | TSkip | TLet x (v -> x) | TWrite Int x x
  deriving Functor

data Param = Param
  { getINTMAX₁ :: Int -- for intermediate results
  , getINTMAX₂ :: Int -- for intermediate variables
  , getINTMAX₃ :: Int -- for elements in the array
  , getINT₁    :: String
  , getINT₂    :: String
  , getINT₃    :: String
  , getQ       :: Int -- the modulus
  }

--
-- Lazy Modulo Insertion
--

type Iv   = (Int, Int)
type St   = Int -> Iv
type Ev v = Eq v => v -> Iv
newtype Ins v x
  = Ins { evalIns :: St -> Ev v -> (x, Iv) }
  deriving Functor

τInsert :: forall v. Eq v => Param
  ->  forall x. (Term v x -> x)
  -> Term v (Ins v x)
  -> Ins v x
τInsert p φ t = Ins $ \σ ρ -> case t of
  TLit  n -> (φ (TLit n), (n, n)) ↓ (0, getINTMAX₁ p)
  TRead i -> (φ (TRead i), σ i)
  TVar  v -> (φ (TVar v),  ρ v)
  TModQ e -> evalIns e σ ρ ↓ (0, getQ p - 1)
  TAdd e₁ e₂ ->
    let (r₁, iv₁) = evalIns e₁ σ ρ
        (r₂, iv₂) = evalIns e₂ σ ρ
    in DT.traceShow (σ 0) (φ (TAdd r₁ r₂), iv₁ +♯ iv₂) ↓ (0, getINTMAX₁ p)
  TSub e₁ e₂ ->
    let (r₁, iv₁) = evalIns e₁ σ ρ
        (r₂, iv₂) = evalIns e₂ σ ρ
    in (φ (TSub r₁ r₂), iv₁ -♯ iv₂)
       ↓ (0, getINTMAX₁ p)
  TMul e₁ e₂ ->
    let (r₁, iv₁) = evalIns e₁ σ ρ
        (r₂, iv₂) = evalIns e₂ σ ρ
    in (φ (TMul r₁ r₂), iv₁ ×♯ iv₂) ↓ (0, getINTMAX₁ p)
  TSkip -> (φ TSkip, undefined)
  TLet e h ->
    let (r, iv) = evalIns e σ ρ ↓ (0, getINTMAX₂ p)
        h' v    = fst $ evalIns (h v) σ ρ'
          where ρ' w | w == v = iv | otherwise = ρ w
    in (φ (TLet r h'), undefined)
  TWrite i e s ->
    let (r, iv) = evalIns e σ ρ ↓ (0, getINTMAX₃ p)
        (s', _) = evalIns s σ' ρ
          where  σ' j | i == j = iv | otherwise = σ j
    in (φ (TWrite i r s'), undefined)
  where (⊆) :: Iv -> Iv -> Bool
        (+♯) :: Iv -> Iv -> Iv
        (-♯) :: Iv -> Iv -> Iv
        (×♯) :: Iv -> Iv -> Iv
        (e, iv₁) ↓ iv₂
          | iv₁ ⊆ iv₂ = (e, iv₁)
          | otherwise = (φ (TModQ e), (0, q - 1))
          where q = getQ p
        (x₁, y₁) ⊆ (x₂, y₂) = x₂ <= x₁ && y₁ <= y₂
        (x₁, y₁) +♯ (x₂, y₂) = (x₁ + x₂, y₁ + y₂)
        (x₁, y₁) -♯ (x₂, y₂) = (x₁ - y₂, y₁ - x₂)
        (x₁, y₁) ×♯ (x₂, y₂) = (minimum a, maximum a)
          where a = [ x₁ * x₂, x₁ * y₂, y₁ * x₂, y₁ * y₂]

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

τUnroll :: Ω -> forall v x. (Term v x -> x)
  -> Trail (Int, Int, Int) x -> x
τUnroll getΩ φ trail = case trail of
  TrHalt -> φ TSkip
  TrNode (s, k, j) x ->
    let m = 2 ^ s; o = 2 ^ (s - 1) - 1 in
      φ (TLet (φ (TRead (k + j)))
          (\u ->
          φ (TLet (φ (TMul
                        (φ (TRead (k + j + m `div` 2)))
                        (φ (TLit (getΩ (o + j))))))
               (\t -> φ (TWrite (k + j) (φ (TAdd (φ (TVar u)) (φ (TVar t))))
                          (φ (TWrite (k + j + m `div` 2)
                               (φ (TSub (φ (TVar u)) (φ (TVar t)))) x)))))))

--
-- Generating C programs
--

type Name   = String
type Gensym = State Int

gensym :: Gensym Name
gensym = do i <- get; modify succ; return ("x" ++ show i)
          
φGen :: Param -> Term Name (Gensym String) -> Gensym String
φGen p t = case t of
  TLit n -> return (show n)
  TRead n -> return ("A[" ++ show n ++ "]")
  TVar v -> return v
  TModQ e -> e <&> (++ (" % " ++ show (getQ p)))
  TAdd a b -> printInfix "+" a b
  TSub a b -> printInfix "-" a b
  TMul a b -> printInfix "*" a b
  TSkip    -> return ""
  TLet e h -> do
    a <- e; name <- gensym; b <- h name
    return ("  " ++ getINT₂ p ++ " " ++ name ++ " = " ++ a ++ ";\n" ++ b)
  TWrite i e s -> do
    a <- e
    (("  A[" ++ show i ++ "] = " ++ a ++ ";\n") ++) <$> s
  where printInfix op =
          let coerce s = "(" ++ getINT₁ p ++ ")" ++ s
          in liftM2 $ \s₁ s₂ ->
            "(" ++ coerce s₁ ++ " " ++ op ++ " " ++ coerce s₂ ++ ")"

-- Generator

hylo :: (Functor f) => (f b -> b, a -> f a) -> a -> b
hylo (φ, ψ) = fix (\f -> φ . fmap f . ψ)

newHopeParam :: Param
newHopeParam = Param
  { getINTMAX₁ = fromIntegral (maxBound :: Word32)
  , getINTMAX₂ = fromIntegral (maxBound :: Word16)
  , getINTMAX₃ = fromIntegral (maxBound :: Word16)
  , getINT₁ = "uint32_t"
  , getINT₂ = "uint16_t"
  , getINT₃ = "uint16_t"
  , getQ    = 12289 }

newHopePrimRoots :: A.Array Int Int
newHopePrimRoots = Prim.primRootArray $ Prim.PRParam
  { Prim.n = 1024, Prim.q    = 12289
  , Prim.ω = 49, Prim.factor = 1 `shiftL` 16 }

newHopeNTT :: String
newHopeNTT =
  hylo (τUnroll (newHopePrimRoots!) (τInsert newHopeParam (φGen newHopeParam))
       , ψTrail 10) (1, 0, 0)
  & (\m -> evalIns m (const (0, getQ newHopeParam - 1)) undefined)
  & fst & flip evalState 0

outputNTT :: Param -> FilePath -> String -> IO ()
outputNTT p path = writeFile path . wrapHeader . wrapFunc
  where wrapFunc s = "void ntt(" ++ getINT₃ p ++ "* A) {\n" ++ s ++ "}"
        wrapHeader = ("#include <stdint.h>\n\n" ++)
