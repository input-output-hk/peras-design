{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Simulate (
  simulate
, simulation
, writeReport
, writeTrace
) where

import Control.Monad.Class.MonadTime (MonadTime(getCurrentTime))
import Control.Monad.IOSim (Failure, IOSim, SimTrace, ppTrace, runSimStrictShutdown, runSimTrace, traceResult)
import Control.Monad.Random (runRand)
import Peras.IOSim.Network (createNetwork, randomTopology, runNetwork)
import Peras.IOSim.Network.Types (NetworkState)
import Peras.IOSim.Node (initializeNodes)
import Peras.IOSim.Protocol.Types (Protocol)
import Peras.IOSim.Simulate.Types (Parameters(..))
import System.Random (mkStdGen)

import qualified Data.Aeson as A
import qualified Data.ByteString.Lazy.Char8 as LBS8

simulation
  :: Parameters
  -> Protocol
  -> IOSim s (NetworkState ())
simulation parameters@Parameters{..} protocol =
  let
    gen = mkStdGen randomSeed
  in
    do
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

simulate
  :: Parameters
  -> Protocol
  -> Bool
  -> (Either Failure (NetworkState ()), Maybe (SimTrace (NetworkState ())))
simulate parameters protocol False = (runSimStrictShutdown $ simulation parameters protocol, Nothing)
simulate parameters protocol True =
  let
    trace = runSimTrace $ simulation parameters protocol
  in
    (traceResult True trace, Just trace)

writeTrace
  :: Show v
  => FilePath
  -> SimTrace (NetworkState v)
  -> IO ()
writeTrace filename = writeFile filename . ppTrace

writeReport
  :: A.ToJSON v
  => FilePath
  -> NetworkState v
  -> IO ()
writeReport filename = LBS8.writeFile filename . A.encode
