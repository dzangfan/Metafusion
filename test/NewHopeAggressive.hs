{-# LANGUAGE LambdaCase #-}

module Main where

import Control.Monad
import Control.Monad.Except
import Control.Monad.IO.Class
import Control.Monad.State
import Data.Function
import LazyModuloInsertion
import System.Environment (getArgs)

type Effect = StateT Threshold (ExceptT (Maybe Threshold) IO) 

main :: IO ()
main = do
  s <- getArgs
  c <- case s of
    [x] -> return (read x :: Int)
    _   -> error ("Invalid arguments: " ++ show s)
  when (c < 0) (error ("Negative argument: " ++ show c))
  let m :: Int
      m = ceiling (1024 / fromIntegral (c + 1) :: Float)
      θ₀ :: Threshold
      θ₀ =
        \case n | n `mod` m == 0 && n /= 0 -> 5
                | otherwise                -> 4
  Left r <- search
    & flip runStateT θ₀
    & runExceptT
  case r of
    Nothing -> putStrLn "Failed."
    Just θ -> do
      let p@(Point (bredN, mredN)) = newHopeModulos θ
      putStrLn ("Ok. " ++ show p)
      let threshold = [i | i <- [0..1023], θ i > 4]
      outputNTT ("c/newHopeNTT" ++ show c ++ ".c")
        [ "Barrett Reduction: " ++ show bredN
        , "Montgomery Reduction: " ++ show mredN
        , show threshold ]
        (newHopeNTT θ)
      putStrLn "Done."

search :: (MonadIO m, MonadState Threshold m, MonadError (Maybe Threshold) m) => m ()
search = forever $ do
  θ <- get
  case newHopeVerif θ of
    Right _ -> throwError (Just θ)
    Left (s, i) -> do
      let θi = θ i
      liftIO $
        putStrLn ("Dead at A[" ++ show i ++ "]. "
                  ++ s ++ ", θ(" ++ show i ++ ") = " ++ show θi ++ "\n")
      when (θi == 0) $ throwError Nothing
      put (\case j | j == i -> (θi - 1) | otherwise -> θ j)
      
