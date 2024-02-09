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
import Peras.Chain (Chain(Genesis))
import Peras.IOSim.Message.Types (InEnvelope(inMessage), OutEnvelope(Idle))
import Peras.IOSim.Network.Types (Topology(..))
import Peras.IOSim.Node.Types (NodeProcess(..), NodeState(..))
import Peras.Message (Message(..), NodeId)

import qualified Data.Map.Strict as M
import qualified Data.Set as S

initializeNodes
  :: UTCTime
  -> Topology
  -> M.Map NodeId (NodeState t)
initializeNodes now Topology{connections} = initializeNode now `M.mapWithKey` connections
  
initializeNode
  :: UTCTime
  -> NodeId
  -> S.Set NodeId
  -> NodeState t
initializeNode clock nodeId downstreams =
  let
    slot = 0
    vrfOutput = 0
    preferredChain = Genesis
  in
    NodeState{..}

runNode
  :: MonadSay m
  => MonadSTM m
  => MonadTime m
  => NodeState t
  -> NodeProcess t m
  -> m ()
runNode initial NodeProcess{..} =
  let
    go state =
      do
        now <- getCurrentTime
        atomically (inMessage <$> readTQueue incoming) >>= \case
          NextSlot slot -> say $ "New slot: " <> show slot
          SomeBlock _ -> say "Some block."
          NewChain _ -> say "New chain."
        atomically $ writeTQueue outgoing $ Idle now
        go state
  in
    go initial  
