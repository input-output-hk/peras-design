{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Simulate (
  simulate
) where

import Control.Monad.Class.MonadTime (MonadTime(getCurrentTime))
import Control.Monad.IOSim (ppTrace, runSimTrace)
import Control.Monad.Random (runRand)
import Peras.IOSim.Network (createNetwork, randomTopology, runNetwork)
import Peras.IOSim.Node (initializeNodes)
import Peras.IOSim.Protocol.Types (Protocol)
import Peras.IOSim.Simulate.Types (Parameters(..))
import System.Random (mkStdGen)

simulate
  :: Parameters
  -> Protocol
  -> IO ()
simulate parameters@Parameters{..} protocol =
  let
    gen = mkStdGen randomSeed
    result =
      runSimTrace
        $ do
          now <- getCurrentTime
          let
            ((states, topology), gen') =
              flip runRand gen
                $ do
                  topology' <- randomTopology parameters
                  states' <- initializeNodes parameters protocol now topology'
                  pure (states', topology')
          network <- createNetwork topology
          runNetwork gen' states network endSlot
  in
    mapM_ putStrLn . lines
      $ ppTrace result
