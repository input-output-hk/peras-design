{-# LANGUAGE LambdaCase #-}

import Control.Monad (replicateM, void)
import Control.Monad.State (runStateT)
import qualified Data.Aeson as A
import qualified Data.ByteString.Lazy.Char8 as LBS8
import qualified Data.Set as Set
import Peras.Abstract.Protocol.Crypto (mkParty)
import Peras.Abstract.Protocol.Environment (mkSimpleScenario)
import Peras.Abstract.Protocol.Network (initialNetwork, runNetwork, simulateNetwork)
import Peras.Abstract.Protocol.Trace (perasTracer)
import Peras.Abstract.Protocol.Types (PerasParams (..), systemStart)
import Peras.Abstract.Protocol.Visualizer (makeVisTracer, visualize, writeGraph)
import System.Environment (getArgs)

main :: IO ()
main =
  getArgs >>= \case
    [] -> singleMain
    ["single"] -> singleMain
    ["multinode"] -> multinodeMain
    _ -> putStrLn "USAGE: peras (single | multinode)"

singleMain :: IO ()
singleMain = mkSimpleScenario >>= simulateNetwork perasTracer >>= print

multinodeMain :: IO ()
multinodeMain =
  do
    (tracer, reader) <- makeVisTracer
    let
      parties =
        Set.fromList
          [ mkParty 1 [2, 10, 25, 33, 39, 56, 71, 96, 101, 108, 109, 115] [1, 2, 6]
          , mkParty 2 [12, 17, 33, 44, 50, 67, 75, 88, 105] [2, 3, 5, 6]
          , mkParty 3 [5, 15, 42, 56, 71, 82, 124] [3, 4, 5, 6]
          , mkParty 4 [8, 15, 21, 38, 50, 65, 127] [1, 5]
          ]
    net <-
      initialNetwork tracer parties systemStart $
        MkPerasParams
          { perasU = 20
          , perasA = 2160
          , perasR = 2
          , perasK = 3
          , perasL = 15
          , perasτ = 2
          , perasB = 100
          , perasΔ = 2
          }
    void $ runStateT (replicateM 130 $ runNetwork tracer mempty) net
    events <- reader
    mapM_ (LBS8.putStrLn . A.encode) events
    writeGraph "tmp.dot" $ visualize events