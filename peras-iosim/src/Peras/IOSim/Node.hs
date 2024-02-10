{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Node (
  NodeProcess(..)
, initializeNode
, initializeNodes
, runNode
) where

import Control.Concurrent.Class.MonadSTM (MonadSTM, atomically)
import Control.Concurrent.Class.MonadSTM.TQueue (TQueue, readTQueue, writeTQueue)
import Control.Lens ((&), (.~), (^.))
import Control.Monad (replicateM)
import Control.Monad.Class.MonadTime (MonadTime(..), UTCTime)
import Control.Monad.Class.MonadTimer (MonadDelay(..))
import Control.Monad.Random (Rand, getRandom, getRandomR)
import Data.Default (Default)
import GHC.Generics (Generic)
import Peras.Block (PartyId(MkPartyId))
import Peras.Chain (Chain(Genesis))
import Peras.Crypto (VerificationKey(VerificationKey))
import Peras.IOSim.Message.Types (InEnvelope(..), OutEnvelope(..), OutMessage(..))
import Peras.IOSim.Network.Types (Topology(..))
import Peras.IOSim.Node.Types (NodeState(NodeState), clock, nodeId, downstreams)
import Peras.IOSim.Protocol (nextSlot, newChain)
import Peras.IOSim.Protocol.Types (Protocol)
import Peras.IOSim.Simulate.Types (Parameters(..))
import Peras.Message (Message(..), NodeId)
import System.Random (RandomGen (..))

import qualified Data.ByteString as BS
import qualified Data.Map.Strict as M
import qualified Data.Set as S

data NodeProcess v m =
  NodeProcess
  {
    incoming :: TQueue m (InEnvelope v)
  , outgoing :: TQueue m (OutEnvelope v)
  }
    deriving stock (Generic)

initializeNodes
  :: RandomGen g
  => Parameters
  -> UTCTime
  -> Topology
  -> Rand g (M.Map NodeId (NodeState v))
initializeNodes parameters now Topology{connections} =
  sequence $ initializeNode parameters now `M.mapWithKey` connections
  
initializeNode
  :: RandomGen g
  => Parameters
  -> UTCTime
  -> NodeId
  -> S.Set NodeId
  -> Rand g (NodeState v)
initializeNode Parameters{maximumStake} clock' nodeId' downstreams' =
  NodeState nodeId'
    <$> (MkPartyId . VerificationKey . BS.pack <$> replicateM 6 getRandom)
    <*> pure clock'
    <*> pure 0
    <*> getRandomR (1, maximumStake)
    <*> getRandomR (0, 1)
    <*> pure Genesis
    <*> pure downstreams'
    <*> pure False
    <*> pure False

runNode
  :: Default v
  => MonadDelay m
  => MonadSTM m
  => MonadTime m
  => RandomGen g
  => g
  -> Parameters
  -> Protocol
  -> NodeState v
  -> NodeProcess v m
  -> m ()
runNode gen0 parameters protocol state0 NodeProcess{..} =
  let
    go gen state =
      do
        now <- getCurrentTime
        atomically (readTQueue incoming) >>= \case
          InEnvelope{..} ->
            do
              ((state', message), gen') <-
                case inMessage of
                  NextSlot slot ->
                    do
                      threadDelay 1000000
                      pure $ nextSlot gen parameters protocol slot state
                  SomeBlock _ -> error "Block transfer not implemented."
                  NewChain chain -> pure $ newChain gen parameters protocol chain state
              atomically
                $ do
                  case message of
                    Nothing -> pure ()
                    Just message' ->
                      mapM_ (writeTQueue outgoing . OutEnvelope now (state ^. nodeId) (SendMessage message') 0)
                        $ S.toList $ state ^. downstreams
                  writeTQueue outgoing . Idle now $ state ^. nodeId
              go gen' $ state' & clock .~ now
          Stop ->
            atomically . writeTQueue outgoing $ Exit now (state ^. nodeId) state
  in
    do
      go gen0 state0
