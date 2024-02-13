{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Peras.IOSim.Network (
  connectNode,
  createNetwork,
  emptyTopology,
  randomTopology,
  runNetwork,
) where

import Control.Concurrent.Class.MonadSTM (MonadSTM, atomically)
import Control.Concurrent.Class.MonadSTM.TQueue (flushTQueue, newTQueueIO, tryReadTQueue, writeTQueue)
import Control.Lens (use, uses, (%=), (^.))
import Control.Monad (unless)
import Control.Monad.Class.MonadFork (MonadFork (forkIO))
import Control.Monad.Class.MonadSay (MonadSay (say))
import Control.Monad.Class.MonadTime (MonadTime)
import Control.Monad.Class.MonadTimer (MonadDelay (..))
import Control.Monad.Random (Rand, getRandomR)
import Control.Monad.State (StateT, evalStateT, get, lift)
import Data.Default (Default (def))
import Data.Foldable (foldlM, foldrM)
import Data.List (delete)
import Peras.Block (Slot)
import Peras.IOSim.Message.Types (InEnvelope (..), OutEnvelope (..), OutMessage (..))
import Peras.IOSim.Network.Types (
  Network (..),
  NetworkState,
  Topology (..),
  activeNodes,
  chainsSeen,
  exitStates,
  lastSlot,
  lastTime,
  pending,
 )
import Peras.IOSim.Node (NodeProcess (NodeProcess), runNode)
import Peras.IOSim.Node.Types (NodeState, stake)
import Peras.IOSim.Protocol.Types (Protocol)
import Peras.IOSim.Simulate.Types (Parameters (..))
import Peras.Message (Message (..), NodeId (..))
import System.Random (RandomGen (..), uniformR)

import qualified Data.Map.Strict as M
import qualified Data.Set as S

emptyTopology ::
  [NodeId] ->
  Topology
emptyTopology = Topology . M.fromList . fmap (,S.empty)

randomTopology ::
  RandomGen g =>
  Parameters ->
  Rand g Topology
randomTopology Parameters{..} =
  let nodeIds = MkNodeId . ("N" <>) . show <$> [1 .. peerCount]
      choose 0 _ = pure mempty
      choose n js =
        do
          j <- (js !!) <$> getRandomR (0, length js - 1)
          (j :) <$> choose (n - 1) (j `delete` js)
      randomConnects i topology =
        foldr (connectNode (nodeIds !! i) . (nodeIds !!)) topology
          <$> choose downstreamCount [0 .. peerCount - 1]
   in foldrM randomConnects (emptyTopology nodeIds) [0 .. peerCount - 1]

connectNode ::
  NodeId ->
  NodeId ->
  Topology ->
  Topology
connectNode upstream downstream = Topology . M.insertWith (<>) upstream (S.singleton downstream) . connections

createNetwork ::
  MonadSTM m =>
  Topology ->
  m (Network v m)
createNetwork Topology{connections} =
  do
    nodesIn <- mapM (const newTQueueIO) connections
    nodesOut <- newTQueueIO
    pure Network{..}

-- TODO: Replace this centralized router with a performant decentralized
--       one like a tree barrier.
-- TODO: Rewrite as a state machine.
runNetwork ::
  forall m g v.
  Default v =>
  Ord v =>
  MonadDelay m =>
  MonadFork m =>
  MonadSay m =>
  MonadSTM m =>
  MonadTime m =>
  RandomGen g =>
  g ->
  Parameters ->
  Protocol ->
  M.Map NodeId (NodeState v) ->
  Network v m ->
  Slot ->
  m (NetworkState v)
runNetwork gen0 parameters protocol states Network{..} endSlot =
  do
    let
      -- Find the total stake.
      total = sum $ (^. stake) <$> states
      -- Split the random number generator.
      (gen1, gen2) = split gen0
      -- FIXME: Needless to say, the random number generation here is messy. We need to add `MonadRandom` to a transformer stack.
      gens = M.fromList $ zip (M.keys states) (splitGen gen2 $ M.size states + 1)
      -- Start a node process.
      forkNode nodeId nodeIn =
        forkIO
          . runNode (gens M.! nodeId) parameters protocol total (states M.! nodeId)
          $ NodeProcess nodeIn nodesOut
      -- Send a message and mark the destination as active.
      output destination inChannel inEnvelope =
        do
          lift . atomically . writeTQueue inChannel $ inEnvelope
          activeNodes %= S.insert destination
      -- Notify a node of the next slot.
      notifySlot destination nodeIn = output destination nodeIn . InEnvelope Nothing . NextSlot =<< use lastSlot
      -- Notify a node to stop.
      notifyStop destination nodeIn = output destination nodeIn Stop
      -- Route one message.
      route gen out@OutEnvelope{..} =
        do
          lastTime %= max timestamp
          pendings <- use pending
          let (r, gen') = uniformR (0, 1) gen
          -- Send the message if it was already pending or if it was received in the current slot.
          -- FIXME: This is an approximation.
          if out `elem` pendings || r > messageDelay parameters
            then case outMessage of
              -- FIXME: Implement this.
              FetchBlock _ -> lift $ say "Fetching blocks is not yet implemented."
              -- Forward the message to the appropriate node.
              SendMessage message ->
                do
                  -- FIXME: Awkwardly peek at the chain.
                  case message of
                    NewChain chain -> chainsSeen %= S.insert chain
                    _ -> pure ()
                  -- Forward the message.
                  output destination (nodesIn M.! destination) $ InEnvelope (pure source) message
            else pending %= (out :)
          pure gen'
      route gen Idle{..} =
        do
          lastTime %= max timestamp
          activeNodes %= S.delete source
          pure gen
      route gen Exit{..} =
        do
          lastTime %= max timestamp
          activeNodes %= S.delete source
          exitStates %= M.insert source nodeState
          pure gen
      -- Read all of the pending messages.
      flush =
        if False -- FIXME: Is it safe to use `flushTQueue`?
          then flushTQueue nodesOut -- As of `io-classes-1.3.1.0`, the queue isn't empty after this call!
          else tryReadTQueue nodesOut >>= maybe (pure mempty) ((<$> flush) . (:))
      -- Wait for all nodes to exit.
      waitForExits gen5 =
        do
          allIdle <- activeNodes `uses` null
          received <- lift $ atomically flush
          gen' <- foldlM route gen5 received
          unless allIdle $ waitForExits gen'
      -- Receive and send messages.
      loop :: MonadDelay m => MonadSay m => g -> StateT (NetworkState v) m (NetworkState v)
      loop gen3 =
        do
          -- Advance the slot counter and notify the nodes, if all nodes are idle.
          allIdle <- activeNodes `uses` null
          -- FIXME: This is unsafe because a node crashing or becoming unresponsive will block the slot advancement.
          gen4 <-
            if allIdle
              then do
                -- FIXME: This is unsafe because a node might take more than one slot to do its computations.
                lastSlot %= (+ 1)
                uncurry notifySlot `mapM_` M.toList nodesIn
                lift $ threadDelay 1000000
                -- FIXME: Assume that pending messages are received in the next slot.
                gen' <- foldlM route gen3 =<< use pending
                pending %= mempty
                pure gen'
              else pure gen3
          -- Receive and route messages.
          received <- lift $ atomically flush
          gen5 <- foldlM route gen4 received
          -- Check on whether the simulation is ending.
          doExit <- lastSlot `uses` (>= endSlot)
          if doExit
            then do
              uncurry notifyStop `mapM_` M.toList nodesIn
              waitForExits gen5
              get
            else loop gen5
    -- Start the node processes.
    uncurry forkNode `mapM_` M.toList nodesIn
    -- Run the network.
    loop gen1 `evalStateT` def

splitGen ::
  RandomGen g =>
  g ->
  Int ->
  [g]
splitGen gen 0 = pure gen
splitGen gen n =
  let (gen', gen'') = split gen
   in gen' : splitGen gen'' (n - 1)
