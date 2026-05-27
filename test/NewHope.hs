module Main (main) where

import Criterion.Main
import LazyModuloInsertion

main :: IO ()
main = defaultMain
  [
    bgroup "GP" [ bench "F"  $ nf newHopeNTT safeThreshold
               , bench "NF" $ nf newHopeNTT safeThreshold ]
  -- , bgroup "IA" [ bench "F"  $ whnf newHopeVerif safeThreshold
  --               , bench "NF" $ whnf newHopeVerifNF safeThreshold ]
  , bgroup "CM" [ bench "F"  $ nf (pointNF.newHopeModulos) safeThreshold
                , bench "NF" $ nf (pointNF.newHopeModulosNF) safeThreshold ]
  ]
  
pointNF :: Point -> Int
pointNF (Point (a, b)) = a + b
