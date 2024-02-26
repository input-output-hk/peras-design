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
import Control.Lens (use, uses, (.=), (^.))
import Control.Monad (replicateM)
import Control.Monad.Class.MonadTime (MonadTime (..), UTCTime)
import Control.Monad.Class.MonadTimer (MonadDelay (..))
import Control.Monad.Random (RandomGen, mkStdGen, runRandT)
import Control.Monad.Random.Class (
  MonadRandom (getRandom, getRandomR),
 )
import Control.Monad.State (
  MonadState (get),
  MonadTrans (lift),
  StateT,
  evalStateT,
 )
import GHC.Generics (Generic)
import Peras.Block (PartyId (MkPartyId))
import Peras.Chain (Chain (Genesis))
import Peras.Crypto (VerificationKey (VerificationKey))
import Peras.IOSim.Message.Types (InEnvelope (..), OutEnvelope (..), OutMessage (..))
import Peras.IOSim.Network.Types (Topology (..))
import Peras.IOSim.Node.Types (NodeState (NodeState), clock, downstreams, initialSeed, nodeId, preferredChain)
import Peras.IOSim.Protocol (newChain, newVote, nextSlot)
import Peras.IOSim.Protocol.Types (Protocol)
import Peras.IOSim.Simulate.Types (Parameters (..))
import Peras.IOSim.Types (Coin)
import Peras.Message (Message (..), NodeId)

import qualified Data.ByteString as BS
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
    <$> (MkPartyId . VerificationKey . BS.pack <$> replicateM 6 getRandom)
    <*> getRandom
    <*> pure clock'
    <*> pure 0
    <*> getRandomR (1, maximumStake)
    <*> getRandomR (0, 1)
    <*> pure Genesis
    <*> pure mempty
    <*> pure downstreams'
    <*> pure False
    <*> pure False

runNode ::
  forall m.
  MonadDelay m =>
  MonadSTM m =>
  MonadTime m =>
  Protocol ->
  Coin ->
  NodeState ->
  NodeProcess m ->
  m ()
runNode protocol total state NodeProcess{..} =
  let go :: MonadDelay m => MonadSTM m => MonadTime m => RandomGen g => g -> StateT NodeState m ()
      go gen =
        do
          let atomically' = lift . atomically
              runRand = flip runRandT gen
          nodeId' <- use nodeId
          downstreams' <- downstreams `uses` S.toList
          now <- lift getCurrentTime
          atomically' (readTQueue incoming)
            >>= \case
              InEnvelope{..} ->
                do
                  (messages, gen') <-
                    case inMessage of
                      NextSlot slot ->
                        do
                          lift $ threadDelay 1000000
                          runRand $ nextSlot protocol slot total
                      SomeBlock block -> runRand $ newVote protocol block
                      NewChain chain -> runRand $ newChain protocol chain
                  bestChain <- use preferredChain
                  atomically' $
                    do
                      mapM_ (\message' -> mapM_ (writeTQueue outgoing . OutEnvelope now nodeId' (SendMessage message') 0) downstreams') messages
                      writeTQueue outgoing $ Idle now nodeId' bestChain
                  clock .= now
                  go gen'
              Stop -> atomically' . writeTQueue outgoing . Exit now nodeId' =<< get
   in go (mkStdGen $ state ^. initialSeed) `evalStateT` state
