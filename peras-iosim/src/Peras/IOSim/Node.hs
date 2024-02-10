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
import Control.Monad.Class.MonadSay (MonadSay(say))
import Control.Monad.Class.MonadTime (MonadTime(..), UTCTime)
import Control.Monad.Random (Rand, getRandomR)
import GHC.Generics (Generic)
import Peras.Chain (Chain(Genesis))
import Peras.IOSim.Message.Types (InEnvelope(..), OutEnvelope(..))
import Peras.IOSim.Network.Types (Topology(..))
import Peras.IOSim.Node.Types (NodeState(..))
import Peras.IOSim.Protocol.Types (Protocol)
import Peras.IOSim.Simulate.Types (Parameters(..))
import Peras.Message (Message(..), NodeId)
import System.Random (RandomGen (..))

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
initializeNode Parameters{maximumStake} clock nodeId downstreams =
  do
    let
      slot = 0
      preferredChain = Genesis
    stake <- getRandomR (1, maximumStake)
    vrfOutput <- getRandomR (0, 1)
    pure NodeState{..}

runNode
  :: MonadSay m
  => MonadSTM m
  => MonadTime m
  => RandomGen g
  => g
  -> Parameters
  -> Protocol
  -> NodeState v
  -> NodeProcess v m
  -> m ()
runNode _gen _parameters _protocol initial@NodeState{nodeId} NodeProcess{..} =
  let
    go state =
      do
        now <- getCurrentTime
        atomically (readTQueue incoming) >>= \case
          InEnvelope{..} ->
            do
              case inMessage of
                NextSlot slot -> say $ "New slot: " <> show slot
                SomeBlock _ -> say "Some block."
                NewChain _ -> say "New chain."
              atomically . writeTQueue outgoing $ Idle now nodeId
              go state
          Stop ->
            atomically . writeTQueue outgoing $ Exit now nodeId initial
  in
    go initial  
