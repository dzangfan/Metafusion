module Main where

import           Criterion.Main
import qualified Data.HashSet as S
import qualified Data.Matrix as M
import           Data.Matrix.MatrixMarket (readMatrix, Matrix(PatternMatrix))
import           ShortestPath

main :: IO ()
main = do
  g1 <- sampleCan "test/graphs/can_144.mtx"
  let mw1 = flattenEdges g1
  let n1 = M.nrows mw1
  g2 <- sampleCan "test/graphs/can_161.mtx"
  let mw2 = flattenEdges g2
  let n2 = M.nrows mw2
  g3 <- sampleCan "test/graphs/can_187.mtx"
  let mw3 = flattenEdges g3
  let n3 = M.nrows mw3
  defaultMain
    [ bgroup "can_144"
      [ bench "F" $ whnf (shortestPathC n1 1 (n1 `div` 2)) mw1
      , bench "NF" $ whnf (shortestPathCNF n1 1 (n1 `div` 2)) mw1]
    , bgroup "can_161"
      [ bench "F" $ whnf (shortestPathC n2 1 (n2 `div` 2)) mw2
      , bench "NF" $ whnf (shortestPathCNF n2 1 (n2 `div` 2)) mw2]
    , bgroup "can_187"
      [ bench "F" $ whnf (shortestPathC n3 1 (n3 `div` 2)) mw3
      , bench "NF" $ whnf (shortestPathCNF n3 1 (n3 `div` 2)) mw3]]

sampleCan :: FilePath -> IO (M.Matrix Bool)
sampleCan p = do
  PatternMatrix (r, c) _ _ xs <- readMatrix p
  let s =
        foldr (\(i, j) ss ->
                 if i == j then ss
                 else let i' = fromIntegral i :: Int
                          j' = fromIntegral j :: Int
                      in S.insert (i', j') (S.insert (j', i') ss))
        S.empty xs
  return (M.matrix r c (`S.member` s))
