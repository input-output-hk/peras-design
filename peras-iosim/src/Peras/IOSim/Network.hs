{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Peras.IOSim.Network (
  connectNode
, createNetwork
, emptyTopology
, randomTopology
, runNetwork
) where

import Control.Concurrent.Class.MonadSTM (MonadSTM, atomically)
import Control.Concurrent.Class.MonadSTM.TQueue (flushTQueue, newTQueueIO, writeTQueue)
import Control.Lens ((%=), use, uses)
import Control.Monad (when)
import Control.Monad.Class.MonadFork (MonadFork(forkIO))
import Control.Monad.Class.MonadSay (MonadSay(say))
import Control.Monad.Class.MonadTime (MonadTime)
import Control.Monad.Class.MonadTimer (MonadDelay(..))
import Control.Monad.Random (Rand, getRandomR)
import Control.Monad.State (StateT, evalStateT, lift)
import Data.Default (def)
import Data.Foldable (foldrM)
import Data.List (delete)
import Peras.Block (Slot)
import Peras.IOSim.Message.Types (InEnvelope(..), OutEnvelope(..), OutMessage(..))
import Peras.IOSim.Network.Types (Network(..), Topology(..), NetworkState, activeNodes, lastSlot, lastTime)
import Peras.IOSim.Node (runNode)
import Peras.IOSim.Node.Types (NodeProcess(NodeProcess), NodeState)
import Peras.IOSim.Simulate.Types (Parameters(..))
import Peras.Message (Message(..), NodeId(..))
import System.Random (RandomGen(..))

import qualified Data.Map.Strict as M
import qualified Data.Set as S

emptyTopology :: Topology
emptyTopology = Topology M.empty

randomTopology
  :: RandomGen g
  => Parameters
  -> Rand g Topology
randomTopology Parameters{..} =
  let
    nodeIds = MkNodeId . show <$> [1..peerCount]
    choose 0 _ = pure mempty
    choose n js =
      do
        j <- (js !!) <$> getRandomR (0, length js - 1)
        (j :) <$> choose (n - 1) (j `delete` js)       
    randomConnects i topology =
      foldr (connectNode (nodeIds !! i) . (nodeIds !!)) topology
        <$> choose downstreamCount [0..peerCount-1]
  in
    foldrM randomConnects emptyTopology [0..peerCount-1]

connectNode
  :: NodeId
  -> NodeId
  -> Topology
  -> Topology
connectNode upstream downstream = Topology . M.insertWith (<>) upstream (S.singleton downstream) . connections

createNetwork
  :: MonadSTM m
  => Topology
  -> m (Network t m)
createNetwork Topology{connections} =
  do
    nodesIn <- mapM (const newTQueueIO) connections
    nodesOut <- newTQueueIO
    pure Network{..}

-- TODO: Replace this centralized router with a performant decentralized
--       one like a tree barrier. 
runNetwork
  :: forall m g t
  .  MonadDelay m
  => MonadFork m
  => MonadSay m
  => MonadSTM m
  => MonadTime m
  => RandomGen g
  => g
  -> M.Map NodeId (NodeState t)
  -> Network t m
  -> Slot
  -> m ()
runNetwork gen states Network{..} endSlot =
  do
    let
      -- Split the random number generator.
      gens = M.fromList $ zip (M.keys states) (splitGen gen $ M.size states)
      -- Start a node process.
      forkNode nodeId nodeIn =
        forkIO
          . runNode (gens M.! nodeId) (states M.! nodeId)
          $ NodeProcess nodeIn nodesOut
      -- Send a message and mark the destination as active.
      output destination inChannel inEnvelope =
        do
          lift . atomically . writeTQueue inChannel $ inEnvelope
          activeNodes %= S.insert destination
      -- Notify a node of the next slot.
      notifySlot destination nodeIn = output destination nodeIn . InEnvelope Nothing . NextSlot =<< use lastSlot
      -- Route one message.
      route OutEnvelope{..} =
        do
          lastTime %= max timestamp
          case outMessage of
            -- FIXME: Implement this.
            FetchBlock _ -> lift $ say "Fetching blocks is not yet implemented."
            -- Forward the message to the appropriate node.
            SendMessage message -> output destination (nodesIn M.! destination) $ InEnvelope (pure source) message
      route Idle{..} =
        do
          lastTime %= max timestamp
          activeNodes %= S.delete source
      -- Receive and send messages.
      loop :: MonadSay m => StateT NetworkState m ()
      loop =
        do
          -- Advance the slot counter and notify the nodes, if all nodes are idle.
          allIdle <- activeNodes `uses` null
          -- FIXME: This is unsafe because a node crashing or becoming unresponsive will block the slot advancement.
          when allIdle
            $ do
              -- FIXME: This is unsafe because a node might take more than one slot to do its computations.
              lastSlot %= (+ 1)
              uncurry notifySlot `mapM_` M.toList nodesIn
          -- Receive and route messages.
          received <- lift . atomically $ flushTQueue nodesOut
          mapM_ route received
          -- Check on whether the simulation is ending.
          slot <- use lastSlot
          when (slot < endSlot) loop 
    -- Start the node processes.
    uncurry forkNode `mapM_` M.toList nodesIn
    -- Run the network.
    evalStateT loop def

splitGen
  :: RandomGen g
  => g
  -> Int
  -> [g]
splitGen gen 0 = pure gen
splitGen gen n =
  let
    (gen', gen'') = split gen
  in
    gen' : splitGen gen'' (n - 1)
