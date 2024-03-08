{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Peras.IOSim.Node (
  NodeProcess (..),
  initializeNode,
  initializeNodes,
  runNode,
) where

import Control.Concurrent.Class.MonadSTM (MonadSTM, atomically)
import Control.Concurrent.Class.MonadSTM.TQueue (TQueue, readTQueue, writeTQueue)
import Control.Lens (use, uses, (%=), (.=))
import Control.Monad.Class.MonadSay (MonadSay (..))
import Control.Monad.Class.MonadTime (MonadTime (..), UTCTime)
import Control.Monad.Class.MonadTimer (MonadDelay (..))
import Control.Monad.IOSim.Orphans ()
import Control.Monad.Random.Class (MonadRandom (getRandom, getRandomR))
import Control.Monad.State (
  MonadState (get),
  MonadTrans (lift),
  StateT,
  evalStateT,
 )
import Control.Tracer (Tracer, natTracer, traceWith)
import Data.Default (def)
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import Peras.Event (Event (..))
import Peras.IOSim.Chain.Types (preferredChain)
import Peras.IOSim.Message.Types (InEnvelope (..), OutEnvelope (..), mkUniqueId)
import Peras.IOSim.Network.Types (Topology (..))
import Peras.IOSim.Node.Types (NodeState (NodeState), chainState, clock, downstreams, nodeId, rxBytes, txBytes)
import Peras.IOSim.Protocol (newBlock, newChain, newVote, nextSlot)
import Peras.IOSim.Protocol.Types (Protocol)
import Peras.IOSim.Simulate.Types (Parameters (..))
import Peras.IOSim.Types (Coin, messageSize)
import Peras.Message (Message (..), NodeId (MkNodeId))

import Data.Map (keysSet)
import qualified Data.Map.Strict as M
import qualified Data.Set as S

data NodeProcess m = NodeProcess
  { incoming :: TQueue m InEnvelope
  , outgoing :: TQueue m OutEnvelope
  }
  deriving stock (Generic)

initializeNodes ::
  MonadRandom m =>
  Parameters ->
  UTCTime ->
  Topology ->
  m (M.Map NodeId NodeState)
initializeNodes parameters now Topology{connections} =
  sequence $ initializeNode parameters now `M.mapWithKey` (keysSet <$> connections)

initializeNode ::
  MonadRandom m =>
  Parameters ->
  UTCTime ->
  NodeId ->
  S.Set NodeId ->
  m NodeState
initializeNode Parameters{maximumStake} clock' nodeId' downstreams' =
  NodeState nodeId'
    <$> ((fromIntegral . abs :: Integer -> Natural) <$> getRandom)
    <*> getRandom
    <*> pure clock'
    <*> pure 0
    <*> getRandomR (1, maximumStake)
    <*> getRandomR (0, 1)
    <*> pure def
    <*> pure downstreams'
    <*> pure False
    <*> pure False
    <*> pure mempty
    <*> pure 0
    <*> pure 0

runNode ::
  forall m.
  MonadDelay m =>
  MonadSay m =>
  MonadSTM m =>
  MonadTime m =>
  Tracer m Event ->
  Protocol ->
  Coin ->
  NodeState ->
  NodeProcess m ->
  m ()
runNode tracer protocol total state NodeProcess{..} =
  let go :: Int -> StateT NodeState m ()
      go i =
        do
          let atomically' = lift . atomically
              tracer' = natTracer lift tracer
          nodeId'@(MkNodeId name) <- use nodeId
          downstreams' <- downstreams `uses` S.toList
          now <- lift getCurrentTime
          atomically' (readTQueue incoming)
            >>= \case
              InEnvelope{..} ->
                do
                  (flip . maybe $ pure ()) origin $
                    \origin' -> traceWith tracer' $ Receive inId now origin' nodeId' inMessage
                  messages <-
                    case inMessage of
                      NextSlot slot ->
                        do
                          lift $ threadDelay 1_000_000
                          nextSlot tracer' protocol slot total
                      SomeVote vote -> newVote tracer' protocol vote
                      RollForward block -> newBlock tracer' protocol block
                      NewChain chain -> newChain tracer' protocol chain
                      _ -> say ("Message not handled: " <> show inMessage) >> pure mempty
                  rxBytes %= (+ messageSize inMessage)
                  bestChain <- chainState `uses` preferredChain
                  let out message outId j =
                        OutEnvelope
                          { timestamp = now
                          , source = nodeId'
                          , outMessage = message
                          , outId = mkUniqueId (name, j)
                          , bytes = messageSize message
                          , destination = outId
                          }
                      outEvent OutEnvelope{..} = Send outId now source destination outMessage
                      outEvent _ = error "impossible"
                      outs = zipWith id (concatMap (flip fmap downstreams' . out) messages) [i ..]
                  atomically' $
                    do
                      mapM_ (writeTQueue outgoing) outs
                      writeTQueue outgoing $ Idle now nodeId' bestChain
                  mapM_ (traceWith tracer' . outEvent) outs
                  txBytes %= (\bs -> bs + (sum (messageSize <$> messages) * fromIntegral (length downstreams')))
                  clock .= now
                  go $ i + length outs
              Stop -> atomically' . writeTQueue outgoing . Exit now nodeId' =<< get
   in go 0 `evalStateT` state
