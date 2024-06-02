{-# LANGUAGE LambdaCase #-}

import Control.Monad (replicateM, void)
import Control.Monad.State (runStateT)
import qualified Data.Aeson as A
import qualified Data.ByteString.Lazy.Char8 as LBS8
import Peras.Abstract.Protocol.Environment (mkSimpleScenario)
import Peras.Abstract.Protocol.Network (simConfigExample, simulate, simulateNetwork)
import Peras.Abstract.Protocol.Trace (perasTracer)
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
    void $ simulate tracer simConfigExample
    events <- reader
    mapM_ (LBS8.putStrLn . A.encode) events
    writeGraph "tmp.dot" $ visualize events
