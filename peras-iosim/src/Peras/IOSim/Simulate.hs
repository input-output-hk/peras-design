{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Peras.IOSim.Simulate (
  simulate,
  simulation,
  writeEvents,
  writeReport,
  writeSays,
  writeTrace,
) where

import Control.Lens ((&), (.~))
import Control.Monad.Class.MonadTime (MonadTime (getCurrentTime))
import Control.Monad.IOSim (Failure, IOSim, SimTrace, ppTrace, runSim, runSimTrace, selectTraceEventsDynamic, selectTraceEventsSay, traceM, traceResult)
import Control.Monad.Random (evalRandT)
import Control.Tracer (Tracer (Tracer), emit)
import Data.Default (def)
import Peras.Event (Event)
import Peras.IOSim.Network (createNetwork, randomTopology, runNetwork)
import Peras.IOSim.Network.Types (NetworkState, networkRandom)
import Peras.IOSim.Node (initializeNodes)
import Peras.IOSim.Protocol.Types (Protocol)
import Peras.IOSim.Simulate.Types (Parameters (..))
import System.Random (mkStdGen, split)

import qualified Data.Aeson as A
import qualified Data.ByteString.Lazy.Char8 as LBS8

simulation ::
  forall s.
  Parameters ->
  Protocol ->
  IOSim s NetworkState
simulation parameters@Parameters{..} protocol =
  do
    let (gen, gen') = split $ mkStdGen randomSeed
        tracer :: Tracer (IOSim s) Event
        tracer = Tracer $ emit traceM
    now <- getCurrentTime
    -- FIXME: Read the topology and node states from files.
    (topology, states) <-
      flip evalRandT gen $
        do
          topology' <- randomTopology parameters
          states' <- initializeNodes parameters now topology'
          pure (topology', states')
    network <- createNetwork topology
    runNetwork tracer parameters protocol states network $
      def & networkRandom .~ gen'

simulate ::
  Parameters ->
  Protocol ->
  Bool ->
  (Either Failure NetworkState, Maybe (SimTrace NetworkState))
simulate parameters protocol False = (runSim $ simulation parameters protocol, Nothing)
simulate parameters protocol True =
  let trace = runSimTrace $ simulation parameters protocol
   in (traceResult False trace, Just trace)

writeTrace ::
  FilePath ->
  SimTrace NetworkState ->
  IO ()
writeTrace filename = writeFile filename . ppTrace

writeSays ::
  FilePath ->
  SimTrace NetworkState ->
  IO ()
writeSays filename = writeFile filename . unlines . selectTraceEventsSay

writeEvents ::
  FilePath ->
  SimTrace NetworkState ->
  IO ()
writeEvents filename =
  LBS8.writeFile filename
    . LBS8.unlines
    . fmap A.encode
    . (selectTraceEventsDynamic :: SimTrace NetworkState -> [Event])

writeReport ::
  FilePath ->
  NetworkState ->
  IO ()
writeReport filename = LBS8.writeFile filename . A.encode
