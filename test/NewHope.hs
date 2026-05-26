{-# LANGUAGE LambdaCase #-}

module Main (main) where

import LazyModuloInsertion

main :: IO ()
main = do
  print (newHopeVerifNF θ); print (newHopeModulos θ)
  where θ = \case 1023 -> 6; _ -> 4
  
