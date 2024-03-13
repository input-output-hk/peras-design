{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Peras.IOSim.Node (
  initializeNode,
  initializeNodes,
  makeContext,
  observeNode,
) where

import Control.Monad (forM_)
import Control.Monad.Class.MonadTime (MonadTime (..), UTCTime, diffUTCTime)
import Control.Monad.IOSim.Orphans ()
import Control.Monad.Random.Class (MonadRandom (getRandom, getRandomR))
import Control.Tracer (Tracer, traceWith)
import Data.Default (def)
import Data.Map (keysSet)
import Numeric.Natural (Natural)
import Peras.Block (Slot)
import Peras.Event (Event (CommitteeMember, Compute, Receive, Rolledback, Send, SlotLeader, Trace))
import Peras.IOSim.Message.Types (InEnvelope (..), OutEnvelope (..))
import Peras.IOSim.Network.Types (Topology (..))
import Peras.IOSim.Node.Types (NodeContext (..), NodeResult (..), NodeStats (..), TraceReport (..))
import Peras.IOSim.Nodes (SomeNode (HonestNode))
import Peras.IOSim.Protocol.Types (Protocol)
import Peras.IOSim.Simulate.Types (Parameters (..))
import Peras.IOSim.Types (Coin, simulationStart)
import Peras.Message (NodeId)

import qualified Peras.IOSim.Nodes.Honest as Honest (Node (Node))

import qualified Data.Aeson as A
import qualified Data.Map.Strict as M
import qualified Data.Set as S

initializeNodes ::
  MonadRandom m =>
  Parameters ->
  Topology ->
  m (M.Map NodeId SomeNode)
initializeNodes parameters Topology{connections} =
  sequence $ initializeNode parameters `M.mapWithKey` (keysSet <$> connections)

initializeNode ::
  MonadRandom m =>
  Parameters ->
  NodeId ->
  S.Set NodeId ->
  m SomeNode
initializeNode Parameters{maximumStake} nodeId downstreams =
  fmap HonestNode $
    Honest.Node nodeId
      <$> ((fromIntegral . abs :: Int -> Natural) <$> getRandom)
      <*> getRandomR (1, maximumStake)
      <*> getRandomR (0, 1)
      <*> pure def
      <*> pure downstreams

makeContext ::
  MonadTime m =>
  Tracer m Event ->
  Protocol ->
  Coin ->
  NodeId ->
  m (NodeContext m)
makeContext tracer protocol totalStake self =
  do
    clock <- getCurrentTime
    -- FIXME: Assumes that the slot length is one second.
    let slot = floor . toRational $ clock `diffUTCTime` simulationStart
        traceSelf value = traceWith tracer . Trace . A.toJSON $ TraceValue{..}
    pure NodeContext{..}

observeNode ::
  Monad m =>
  (Event -> m ()) ->
  NodeId ->
  Slot ->
  UTCTime ->
  InEnvelope ->
  NodeResult ->
  m ()
observeNode traceWith' self slot clock InEnvelope{..} NodeResult{outputs, stats = statistics@NodeStats{..}} =
  do
    traceWith' $ Receive inId inTime origin self inMessage inBytes
    forM_ outputs $
      \OutEnvelope{..} -> traceWith' $ Send outId outTime source destination outMessage outBytes
    traceWith' $ Compute self cpuTime
    forM_ rollbacks $ traceWith' . Rolledback self
    forM_ slotLeader $ traceWith' . SlotLeader self
    forM_ committeeMember $ traceWith' . CommitteeMember self
    traceWith' . Trace . A.toJSON $ TraceStats{..}
