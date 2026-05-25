
module Main where

import Control.Monad
import LazyModuloInsertion

main :: IO ()
main = forM_ [0 .. 1023] $ \i -> do
  let θ j | j == i = 5 | otherwise = safeThreshold j
  putStrLn ("Testing... " ++ show i ++ "\n")
  let result = case newHopeVerif θ of
        Left s -> "Dead. " ++ s
        _ -> let Point (bred, mred) = newHopeModulos θ
             in "Ok. Modulos: " ++ show bred ++ " + " ++ show mred
  putStrLn result
