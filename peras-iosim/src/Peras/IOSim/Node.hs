{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
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
import Data.Default (def)
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import Peras.IOSim.Chain.Types (preferredChain)
import Peras.IOSim.Message.Types (InEnvelope (..), OutEnvelope (..), OutMessage (..))
import Peras.IOSim.Network.Types (Topology (..))
import Peras.IOSim.Node.Types (NodeState (NodeState), chainState, clock, downstreams, nodeId, rxBytes, txBytes)
import Peras.IOSim.Protocol (newBlock, newChain, newVote, nextSlot)
import Peras.IOSim.Protocol.Types (Protocol)
import Peras.IOSim.Simulate.Types (Parameters (..))
import Peras.IOSim.Types (Coin, messageSize)
import Peras.Message (Message (..), NodeId)

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
  sequence $ initializeNode parameters now `M.mapWithKey` connections

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
  Protocol ->
  Coin ->
  NodeState ->
  NodeProcess m ->
  m ()
runNode protocol total state NodeProcess{..} =
  let go :: MonadDelay m => MonadSTM m => MonadSay m => MonadTime m => StateT NodeState m ()
      go =
        do
          let atomically' = lift . atomically
          nodeId' <- use nodeId
          downstreams' <- downstreams `uses` S.toList
          now <- lift getCurrentTime
          atomically' (readTQueue incoming)
            >>= \case
              InEnvelope{..} ->
                do
                  messages <-
                    case inMessage of
                      NextSlot slot ->
                        do
                          lift $ threadDelay 1000000
                          nextSlot protocol slot total
                      SomeVote vote -> newVote protocol vote
                      SomeBlock block -> newBlock protocol block
                      NewChain chain -> newChain protocol chain
                  rxBytes %= (+ messageSize inMessage)
                  bestChain <- chainState `uses` preferredChain
                  atomically' $
                    do
                      mapM_ (\message' -> mapM_ (writeTQueue outgoing . OutEnvelope now nodeId' (SendMessage message') 0) downstreams') messages
                      writeTQueue outgoing $ Idle now nodeId' bestChain
                  txBytes %= (\bs -> bs + (sum (messageSize <$> messages) * fromIntegral (length downstreams')))
                  clock .= now
                  go
              Stop -> atomically' . writeTQueue outgoing . Exit now nodeId' =<< get
   in go `evalStateT` state
