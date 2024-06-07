{-# LANGUAGE LambdaCase #-}

module Main where

import Data.Functor ((<&>))
import Peras.Server (runServer)
import System.Environment (getArgs)

main :: IO ()
main = do
  port <-
    getArgs <&> \case
      [p] -> read p
      _ -> 8091
  runServer port
