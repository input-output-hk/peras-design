{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Simulate (
  simulate
, writeReport
, writeTrace
) where

import Control.Monad.Class.MonadTime (MonadTime(getCurrentTime))
import Control.Monad.IOSim (SimTrace, ppTrace, runSimTrace, traceResult)
import Control.Monad.Random (runRand)
import Peras.IOSim.Network (createNetwork, randomTopology, runNetwork)
import Peras.IOSim.Network.Types (NetworkState)
import Peras.IOSim.Node (initializeNodes)
import Peras.IOSim.Protocol.Types (Protocol)
import Peras.IOSim.Simulate.Types (Parameters(..))
import System.Random (mkStdGen)

import qualified Data.Aeson as A
import qualified Data.ByteString.Lazy.Char8 as LBS8

simulate
  :: Parameters
  -> Protocol
  -> SimTrace (NetworkState ())
simulate parameters@Parameters{..} protocol =
  let
    gen = mkStdGen randomSeed
  in
    runSimTrace
      $ do
        now <- getCurrentTime
        let
          ((states, topology), gen') =
            flip runRand gen
              $ do
                topology' <- randomTopology parameters
                states' <- initializeNodes parameters now topology'
                pure (states', topology')
        network <- createNetwork topology
        runNetwork gen' parameters protocol states network endSlot

writeTrace
  :: Show v
  => FilePath
  -> SimTrace (NetworkState v)
  -> IO ()
writeTrace filename trace = writeFile filename $ ppTrace trace

writeReport
  :: A.ToJSON v
  => FilePath
  -> SimTrace (NetworkState v)
  -> IO ()
writeReport filename trace =
  case traceResult True trace of
    Right result -> LBS8.writeFile filename $ A.encode result
    Left failure -> print failure
