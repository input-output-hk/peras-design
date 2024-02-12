module Main (
  main,
) where

import Data.Default (def)
import Peras.RandomForks (execute)
import System.Environment (getArgs)
import System.Random (getStdGen)

main :: IO ()
main =
  do
    args <- getArgs
    gen <- getStdGen
    let parameters = def
    case args of
      [duration, peerFilename, chainFilename] -> execute gen parameters (read duration) peerFilename chainFilename
      _ -> putStrLn "USAGE: random-forks DURATION PEER_FILENAME CHAIN_FILENAME"
