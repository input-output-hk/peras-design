module Main where

import Peras.Conformance.ExternalSpec
import System.Environment
import System.IO
import Test.Hspec

main :: IO ()
main = do
  hWriter <- openFile "simin" AppendMode
  hReader <- openFile "simout" ReadMode
  hSetBuffering hWriter LineBuffering
  hSetBuffering hReader LineBuffering
  hspec $
    spec hReader hWriter
