{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Network (
  connectNode
, createNetwork
, emptyTopology
, runNetwork
) where

import Control.Concurrent.Class.MonadSTM (MonadSTM, atomically)
import Control.Concurrent.Class.MonadSTM.TQueue (flushTQueue, newTQueueIO, writeTQueue)
import Control.Monad (void, when)
import Control.Monad.Class.MonadFork (MonadFork(forkIO))
import Control.Monad.Class.MonadSay (MonadSay)
import Control.Monad.Class.MonadTime (MonadTime)
import Control.Monad.Class.MonadTimer (MonadDelay(..))
import Peras.IOSim.Message.Types (InEnvelope(NewSlot))
import Peras.IOSim.Network.Types (Network(..), Topology(..))
import Peras.IOSim.Node (runNode)
import Peras.IOSim.Node.Types (NodeProcess(NodeProcess), NodeState)
import Peras.IOSim.Types (NodeId, SlotNo)

import qualified Data.Map.Strict as M
import qualified Data.Set as S

emptyTopology :: Topology
emptyTopology = Topology M.empty

connectNode
  :: NodeId
  -> NodeId
  -> Topology
  -> Topology
connectNode upstream downstream = Topology . M.insertWith (<>) upstream (S.singleton downstream) . connections

createNetwork
  :: MonadSTM m
  => Topology
  -> m (Network m)
createNetwork Topology{connections} =
  do
    nodesIn <- mapM (const newTQueueIO) connections
    nodesOut <- newTQueueIO
    pure Network{..}

runNetwork
  :: MonadDelay m
  => MonadFork m
  => MonadSay m
  => MonadSTM m
  => MonadTime m
  => M.Map NodeId NodeState
  -> Network m
  -> SlotNo
  -> m ()
runNetwork states Network{..} endSlot =
  do
    sequence_
      [
        forkIO
          . runNode (states M.! nodeId)
          $ NodeProcess nodeIn nodesOut
      |
        (nodeId, nodeIn) <- M.toList nodesIn
      ]
    let go slotNo =
          do
            let slotNo' = slotNo + 1
            threadDelay 1000000
            sequence_
              [
                atomically $ writeTQueue nodeIn $ NewSlot slotNo'
              |
                (_, nodeIn) <- M.toList nodesIn
              ]
            void . atomically $ flushTQueue nodesOut
            when (slotNo' < endSlot)
              $ go slotNo'
    go 0
