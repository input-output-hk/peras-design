{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Peras.IOSim.Node (
  initializeNode,
  initializeNodes,
  makeContext,
  observeNode,
  stepNode,
) where

import Control.Monad (forM_)
import Control.Monad.Class.MonadTime (MonadTime (..), UTCTime, diffUTCTime)
import Control.Monad.Random.Class (MonadRandom (getRandom, getRandomR))
import Control.Monad.Writer
import Control.Tracer (Tracer, traceWith)
import Data.Default (def)
import Data.Map (keysSet)
import Peras.Event (Event (CommitteeMember, Compute, Receive, Rolledback, Send, SlotLeader, Trace))
import Peras.IOSim.Message.Types (InEnvelope (..), OutEnvelope (..))
import Peras.IOSim.Network.Types (Topology (..))
import Peras.IOSim.Node.Types (NodeContext (..), NodeResult (..), NodeStats (..), PerasNode (..), StepResult (..), TraceReport (..))
import Peras.IOSim.Nodes (SomeNode (HonestNode))
import Peras.IOSim.Protocol.Types (Protocol)
import Peras.IOSim.Simulate.Types (Parameters (..))
import Peras.IOSim.Types (Coin, simulationStart)
import Peras.Message (NodeId)
import Peras.Numbering (SlotNumber)

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
initializeNode Parameters{maximumStake, messageBandwidth} nodeId downstreams =
  fmap HonestNode $
    Honest.Node nodeId
      <$> ((toInteger . abs :: Int -> Integer) <$> getRandom)
      <*> getRandomR (1, maximumStake)
      <*> pure messageBandwidth
      <*> getRandomR (0, 1)
      <*> pure downstreams
      <*> pure def

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
  SlotNumber ->
  UTCTime ->
  InEnvelope ->
  NodeResult ->
  m ()
observeNode _ _ _ _ Stop _ = pure ()
observeNode traceWith' self slot clock InEnvelope{..} NodeResult{outputs, stats = statistics@NodeStats{..}} =
  do
    traceWith' $ Receive inId inTime origin self inMessage inBytes
    forM_ outputs $
      \case
        Idle -> pure ()
        OutEnvelope{..} -> traceWith' $ Send outId outTime source destination outMessage outBytes
    traceWith' $ Compute self cpuTime
    forM_ rollbacks $ traceWith' . Rolledback self
    forM_ slotLeader $ traceWith' . SlotLeader self
    forM_ committeeMember $ traceWith' . CommitteeMember self
    traceWith' . Trace . A.toJSON $ TraceStats{..}

stepNode ::
  PerasNode a =>
  Protocol ->
  Coin ->
  a ->
  SlotNumber ->
  UTCTime ->
  InEnvelope ->
  (StepResult, a)
stepNode protocol totalStake node slot clock input =
  let
    -- Discard custom events.
    traceSelf = const $ pure ()
    -- Record standard events.
    tracer = tell . pure
    ((NodeResult stepTime stepOutputs _, node'), stepEvents) =
      runWriter $ do
        -- Handle the messsage.
        (result, node'') <- handleMessage node NodeContext{..} input
        -- Write the events.
        observeNode tracer (getNodeId node) slot clock input result
        pure (result, node'')
   in
    (StepResult{..}, node')
