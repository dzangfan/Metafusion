{-# LANGUAGE LambdaCase #-}

module Main (main) where

import LazyModuloInsertion

θ :: Threshold
θ x
  | x `elem` [95,223,351,479,607,735,863,991,190,446,702,958,380,892,760] = 5
  | otherwise = 4

main :: IO ()
main = do
  putStrLn $
    case newHopeVerif θ of
      Left s -> "Dead. " ++ s
      Right _ -> "OK. " ++ show (newHopeModulos θ)
  
