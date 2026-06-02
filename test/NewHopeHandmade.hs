module Main where

import LazyModuloInsertion

main :: IO ()
main = case handmadeVerif of
  Left (s, i) -> do
    putStrLn ("Failed at " ++ show i ++ ". " ++ s)
  Right _ -> do
    let Point (bredN, mredN) = handmadeModulos
    print (bredN, mredN)
    outputNTT "c/newHopeNTTHandmade.c"
      [ "Barrett Reduction: " ++ show bredN
      , "Montgomery Reduction: " ++ show mredN]
      handmadeNTT
    putStrLn "Done."
