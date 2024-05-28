{-# LANGUAGE LambdaCase #-}

import Control.Monad (replicateM, void)
import Control.Monad.State (runStateT)
import qualified Data.Set as Set
import Peras.Abstract.Protocol.Crypto (mkParty)
import Peras.Abstract.Protocol.Environment (mkSimpleScenario)
import Peras.Abstract.Protocol.Network (initialNetwork, runNetwork, tickNetwork)
import Peras.Abstract.Protocol.Trace (perasTracer)
import Peras.Abstract.Protocol.Types (systemStart)
import System.Environment (getArgs)

main :: IO ()
main =
  getArgs >>= \case
    [] -> simpleMain
    ["simple"] -> simpleMain
    ["multinode"] -> multinodeMain
    _ -> putStrLn "USAGE: peras (simple | multinode)"

simpleMain :: IO ()
simpleMain = mkSimpleScenario >>= runNetwork perasTracer >>= print

multinodeMain :: IO ()
multinodeMain =
  do
    let
      p1 = mkParty 1 [5, 10, 15] [20]
      p2 = mkParty 2 [8, 12, 17] [20]
    net <- initialNetwork (Set.fromList [p1, p2]) systemStart
    void $ runStateT (replicateM 40 $ tickNetwork perasTracer mempty) net
