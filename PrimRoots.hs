
module PrimRoots where
import Data.Array
import Control.Monad.State
import Control.Monad
import Data.Bits

data PRParam = PRParam
  { n :: Int
  , q :: Int
  , ω :: Int
  , factor :: Int
  }

primRootArray :: PRParam -> Array Int Int
primRootArray param =
  snd $ execState simulation (0, initPowers)
  where simulation = do
          forM_ [1 .. num_stage] $ \s -> do
            let m = 1 `shiftL` s
            let num_butterfly = n param `shiftR` s
            forM_ [0 .. m `div` 2 - 1] $ \j ->
              modify $ \ (idx, arr) ->
              let p = primRootPower param (j * num_butterfly)
              in (idx + 1, arr // [(idx, p)])
        num_stage = lg (n param)
        initPowers = listArray (0, n param - 1) (repeat 1)


primRootPower :: PRParam -> Int -> Int
primRootPower param 0 = factor param `mod` q param
primRootPower param n =
  (ω param `modmul` primRootPower param (n - 1)) param

modmul :: Int -> Int -> PRParam -> Int
modmul a b param = (a * b) `mod` q param

lg :: Int -> Int
lg n = floor (logBase 2 $ fromIntegral n :: Double)
