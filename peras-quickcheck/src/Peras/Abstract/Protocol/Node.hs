{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Peras.Abstract.Protocol.Node where

import Control.Arrow ((&&&))
import Control.Concurrent.Class.MonadSTM (MonadSTM (..))
import Control.Monad (when)
import Control.Monad.Except (ExceptT (ExceptT), runExceptT)
import Control.Monad.State (StateT, gets, lift, modify')
import Control.Tracer (Tracer, traceWith)
import Data.Set (Set)
import Peras.Abstract.Protocol.BlockCreation (blockCreation)
import Peras.Abstract.Protocol.Diffusion (Diffuser (..), defaultDiffuser, diffuseChain, diffuseVote)
import Peras.Abstract.Protocol.Fetching (fetching)
import Peras.Abstract.Protocol.Preagreement (preagreement)
import Peras.Abstract.Protocol.Trace (PerasLog (..))
import Peras.Abstract.Protocol.Types (
  Payload,
  PerasParams,
  PerasResult,
  PerasState,
  defaultParams,
  inRound,
  initialPerasState,
  newRound,
 )
import Peras.Abstract.Protocol.Voting (voting)
import Peras.Block (Party)
import Peras.Chain (Chain, Vote)
import Peras.Numbering (RoundNumber, SlotNumber)

data NodeState m = MkNodeState
  { self :: Party
  , clock :: SlotNumber
  , protocol :: PerasParams
  , stateVar :: TVar m PerasState
  , diffuserVar :: TVar m Diffuser
  }

initialNodeState :: MonadSTM m => Party -> SlotNumber -> m (NodeState m)
initialNodeState self clock =
  do
    let protocol = defaultParams
    stateVar <- newTVarIO initialPerasState
    diffuserVar <- newTVarIO defaultDiffuser
    pure MkNodeState{..}

tick :: forall m. MonadSTM m => Tracer m PerasLog -> Payload -> StateT (NodeState m) m (PerasResult ())
tick tracer payload = do
  params <- gets protocol
  party <- gets self
  state <- gets stateVar
  diffuser <- gets diffuserVar
  -- Increment clock.
  s <- gets $ (1 +) . clock
  modify' $ \node -> node{clock = s}
  let r = inRound s params
  lift $ traceWith tracer $ Tick s r
  -- Retrieve chains and votes to be diffused.
  (newChains, newVotes) <- lift $ (pendingChains &&& pendingVotes) <$> readTVarIO diffuser
  lift . atomically . modifyTVar' diffuser $ \d -> d{pendingChains = mempty, pendingVotes = mempty}
  -- Operate node.
  lift $ tickNode tracer params party state s r payload newChains newVotes diffuser

tickNode ::
  forall m.
  MonadSTM m =>
  Tracer m PerasLog ->
  PerasParams ->
  Party ->
  TVar m PerasState ->
  SlotNumber ->
  RoundNumber ->
  Payload ->
  Set Chain ->
  Set Vote ->
  TVar m Diffuser ->
  m (PerasResult ())
tickNode tracer params party state s r payload newChains newVotes diffuser = do
  -- 1. Get votes and chains from the network.
  runExceptT $ do
    -- 2. Invoke fetching.
    ExceptT $ fetching tracer params party state s newChains newVotes
    -- 3. Invoke block creation if leader.
    ExceptT $ blockCreation params party state s payload (diffuseChain diffuser)
    -- 4. Invoke voting if committee member.
    when (newRound s params) $
      ExceptT $
        voting tracer params party state r preagreement (diffuseVote diffuser)
