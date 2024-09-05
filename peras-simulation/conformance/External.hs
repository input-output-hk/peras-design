module Main where

import qualified Data.Aeson as A
import qualified Data.ByteString.Lazy.Char8 as LBS8
import Peras.Conformance.ExternalSpec (spec)
import Peras.Conformance.Test.External (NodeRequest (Stop))
import System.Environment ()
import System.IO (
  BufferMode (LineBuffering),
  IOMode (AppendMode, ReadMode),
  hSetBuffering,
  openFile,
 )
import Test.Hspec (hspec)

main :: IO ()
main = do
  hWriter <- openFile "simin" AppendMode
  hReader <- openFile "simout" ReadMode
  hSetBuffering hWriter LineBuffering
  hSetBuffering hReader LineBuffering
  hspec $
    spec hReader hWriter
  LBS8.hPutStrLn hWriter $ A.encode Stop
