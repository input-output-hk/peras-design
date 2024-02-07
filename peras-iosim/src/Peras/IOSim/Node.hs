{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Node (
  initializeNode
, initializeNodes
, runNode
) where

import Control.Concurrent.Class.MonadSTM (MonadSTM, atomically)
import Control.Concurrent.Class.MonadSTM.TQueue (readTQueue, writeTQueue)
import Control.Monad.Class.MonadSay (MonadSay(say))
import Control.Monad.Class.MonadTime (MonadTime(..), UTCTime)
import Peras.IOSim.Message.Types (OutEnvelope(Idle), InEnvelope(Stop, InEnvelope, NewSlot))
import Peras.IOSim.Network.Types (Topology(..))
import Peras.IOSim.Node.Types (NodeProcess(..), NodeState(..))
import Peras.IOSim.Types (Chain(Genesis), NodeId)

import qualified Data.Map.Strict as M
import qualified Data.Set as S

initializeNodes
  :: UTCTime
  -> Topology
  -> M.Map NodeId NodeState
initializeNodes now Topology{connections} = initializeNode now `M.mapWithKey` connections
  
initializeNode
  :: UTCTime
  -> NodeId
  -> S.Set NodeId
  -> NodeState
initializeNode clock nodeId downstreams =
  let
    slotNo = 0
    vrfOutput = 0
    preferredChain = Genesis
  in
    NodeState{..}

runNode
  :: MonadSay m
  => MonadSTM m
  => MonadTime m
  => NodeState
  -> NodeProcess m
  -> m ()
runNode initial NodeProcess{..} =
  let
    go state =
      do
        now <- getCurrentTime
        atomically (readTQueue incoming) >>= \case
          InEnvelope message ->
            do
              say $ show message
              atomically $ writeTQueue outgoing $ Idle now
              go state
          NewSlot slot ->
            do
              say $ "New slot: " <> show slot
              atomically $ writeTQueue outgoing $ Idle now
              go state
          Stop -> say "Stopping"
  in
    go initial  
