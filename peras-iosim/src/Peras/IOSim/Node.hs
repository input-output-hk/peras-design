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
import Control.Monad.Random (Rand, getRandomR)
import Peras.Chain (Chain(Genesis))
import Peras.IOSim.Message.Types (InEnvelope(inMessage), OutEnvelope(Idle))
import Peras.IOSim.Network.Types (Topology(..))
import Peras.IOSim.Node.Types (NodeProcess(..), NodeState(..))
import Peras.IOSim.Protocol.Types (Protocol)
import Peras.IOSim.Simulate.Types (Parameters(..))
import Peras.Message (Message(..), NodeId)
import System.Random (RandomGen (..))

import qualified Data.Map.Strict as M
import qualified Data.Set as S

initializeNodes
  :: RandomGen g
  => Parameters
  -> Protocol
  -> UTCTime
  -> Topology
  -> Rand g (M.Map NodeId (NodeState t))
initializeNodes parameters protocol now Topology{connections} =
  sequence $ initializeNode parameters protocol now `M.mapWithKey` connections
  
initializeNode
  :: RandomGen g
  => Parameters
  -> Protocol
  -> UTCTime
  -> NodeId
  -> S.Set NodeId
  -> Rand g (NodeState t)
initializeNode Parameters{maximumStake} protocol clock nodeId downstreams =
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
  -> NodeState t
  -> NodeProcess t m
  -> m ()
runNode _gen initial NodeProcess{..} =
  let
    go state =
      do
        now <- getCurrentTime
        atomically (inMessage <$> readTQueue incoming) >>= \case
          NextSlot slot -> say $ "New slot: " <> show slot
          SomeBlock _ -> say "Some block."
          NewChain _ -> say "New chain."
        atomically $ writeTQueue outgoing $ Idle now (nodeId initial)
        go state
  in
    go initial  
