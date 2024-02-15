{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Peras.IOSim.Network where

import Control.Concurrent.Class.MonadSTM (MonadSTM, STM, TQueue, atomically)
import Control.Concurrent.Class.MonadSTM.TQueue (flushTQueue, newTQueueIO, tryReadTQueue, writeTQueue)
import Control.Lens (
  Field1 (_1),
  Field2 (_2),
  use,
  uses,
  (%=),
  (.=),
  (^.),
 )
import Control.Monad (unless, void)
import Control.Monad.Class.MonadFork (MonadFork (forkIO))
import Control.Monad.Class.MonadSay (MonadSay (say))
import Control.Monad.Class.MonadTime (MonadTime)
import Control.Monad.Class.MonadTimer (MonadDelay (..))
import Control.Monad.Random (MonadRandom, RandT, getRandomR, liftRandT)
import Control.Monad.State (StateT, execStateT, gets, lift)
import Data.Default (Default (def))
import Data.Foldable (foldrM)
import Data.List (delete)
import Data.Maybe (fromMaybe)
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
  MonadRandom m =>
  Parameters ->
  m Topology
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
  Parameters ->
  Protocol ->
  M.Map NodeId (NodeState v) ->
  Network v m ->
  Slot ->
  RandT g m (NetworkState v)
runNetwork parameters protocol states network@Network{..} endSlot =
  liftRandT . (. (def,)) . execStateT $
    do
      let
        -- Notify a node to stop.
        notifyStop destination nodeIn = output destination nodeIn Stop

        -- Receive and send messages.
        loop :: MonadDelay m => MonadSay m => StateT (NetworkState v, g) m (NetworkState v)
        loop =
          do
            stepToIdle parameters network
            -- Check on whether the simulation is ending.
            doExit <- (_1 . lastSlot) `uses` (>= endSlot)
            if doExit
              then do
                uncurry notifyStop `mapM_` M.toList nodesIn
                waitForExits parameters network
                gets fst
              else loop
      -- Start the node processes.
      startNodes parameters protocol states network
      -- Run the network.
      loop

startNodes ::
  (Monad m, RandomGen g, Eq v, MonadSTM m, MonadSay m, Ord v, MonadDelay m, Default v, MonadFork m, MonadTime m) =>
  Parameters ->
  Protocol ->
  M.Map NodeId (NodeState v) ->
  Network v m ->
  StateT (NetworkState v, g) m ()
startNodes parameters protocol states network =
  mapM_ forkNode $ M.toList nodesIn
 where
  Network{nodesIn, nodesOut} = network
  -- Find the total stake.
  total = fromMaybe (sum $ (^. stake) <$> states) $ totalStake parameters
  -- Start a node process.
  forkNode (nodeId, nodeIn) =
    do
      gen <- use _2
      let (gen', gen'') = split gen
      _2 .= gen'
      void
        . lift
        . forkIO
        . runNode gen'' protocol total (states M.! nodeId)
        $ NodeProcess nodeIn nodesOut

-- Wait for all nodes to exit.
waitForExits ::
  (Monad m, RandomGen g, Eq v, MonadSTM m, MonadSay m, Ord v, MonadDelay m) =>
  Parameters ->
  Network v m ->
  StateT (NetworkState v, g) m ()
waitForExits parameters network =
  do
    allIdle <- (_1 . activeNodes) `uses` null
    received <- lift $ atomically (flush nodesOut)
    mapM_ route received
    unless allIdle $ waitForExits parameters network
 where
  Network{nodesOut} = network
  route = routeEnvelope parameters network

-- | Read all of the pending messages.
flush :: MonadSTM m => TQueue m a -> STM m [a]
flush q =
  if False -- FIXME: Is it safe to use `flushTQueue`?
    then flushTQueue q -- As of `io-classes-1.3.1.0`, the queue isn't empty after this call!
    else tryReadTQueue q >>= maybe (pure mempty) ((<$> flush q) . (:))

-- | Advance the network up to one single slot.
-- This function loops until all nodes are idle
stepToIdle ::
  (Monad m, RandomGen g, Eq v, MonadSTM m, MonadSay m, Ord v, MonadDelay m) =>
  Parameters ->
  Network v m ->
  StateT (NetworkState v, g) m ()
stepToIdle parameters network = do
  -- Advance the slot counter and notify the nodes, if all nodes are idle.
  allIdle <- (_1 . activeNodes) `uses` null
  -- FIXME: This is unsafe because a node crashing or becoming unresponsive will block the slot advancement.
  if allIdle
    then do
      -- FIXME: This is unsafe because a node might take more than one slot to do its computations.
      _1 . lastSlot %= (+ 1)
      uncurry notifySlot `mapM_` M.toList nodesIn
      lift $ threadDelay 1000000
      -- FIXME: Assume that pending messages are received in the next slot.
      mapM_ route =<< use (_1 . pending)
      _1 . pending .= mempty
    else do
      -- Receive and route messages.
      received <- lift $ atomically $ flush nodesOut
      mapM_ route received
      stepToIdle parameters network
 where
  Network{nodesIn, nodesOut} = network
  route = routeEnvelope parameters network
  -- Notify a node of the next slot.
  notifySlot destination nodeIn =
    output destination nodeIn . InEnvelope Nothing . NextSlot
      =<< use (_1 . lastSlot)

-- | Dispatch a single message through the network.
routeEnvelope ::
  (Monad m, RandomGen g, Eq v, MonadSTM m, MonadSay m, Ord v) =>
  Parameters ->
  Network v m ->
  OutEnvelope v ->
  StateT (NetworkState v, g) m ()
routeEnvelope parameters Network{nodesIn} = \case
  out@OutEnvelope{..} ->
    do
      _1 . lastTime %= max timestamp
      pendings <- use $ _1 . pending
      (r, gen') <- uniformR (0, 1) <$> use _2
      _2 .= gen'
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
                NewChain chain -> _1 . chainsSeen %= S.insert chain
                _ -> pure ()
              -- Forward the message.
              output destination (nodesIn M.! destination) $ InEnvelope (pure source) message
        else _1 . pending %= (out :)
  Idle{..} -> do
    _1 . lastTime %= max timestamp
    _1 . activeNodes %= S.delete source
  Exit{..} -> do
    _1 . lastTime %= max timestamp
    _1 . activeNodes %= S.delete source
    _1 . exitStates %= M.insert source nodeState

-- Send a message and mark the destination as active.
output :: MonadSTM m => NodeId -> TQueue m p -> p -> StateT (NetworkState v, g) m ()
output destination inChannel inEnvelope =
  do
    lift . atomically . writeTQueue inChannel $ inEnvelope
    _1 . activeNodes %= S.insert destination
