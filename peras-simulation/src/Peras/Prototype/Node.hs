{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Peras.Prototype.Node where

import Control.Concurrent.Class.MonadSTM (MonadSTM (..))
import Control.Monad (when)
import Control.Monad.Except (ExceptT (ExceptT), runExceptT)
import Control.Monad.State (StateT, gets, lift, modify')
import Control.Tracer (Tracer, nullTracer, traceWith)
import Data.Default (def)
import Data.Set (Set)
import Peras.Block (Party)
import Peras.Chain (Chain, Vote)
import Peras.Numbering (RoundNumber, SlotNumber)
import Peras.Prototype.BlockCreation (blockCreation)
import Peras.Prototype.BlockSelection (selectBlock)
import Peras.Prototype.Crypto (mkParty)
import Peras.Prototype.Diffusion (Diffuser, defaultDiffuser, diffuseChain, diffuseVote, popChainsAndVotes)
import Peras.Prototype.Fetching (fetching)
import Peras.Prototype.Trace (PerasLog (..))
import Peras.Prototype.Types (
  Payload,
  PerasParams (perasΔ),
  PerasResult,
  PerasState,
  inRound,
  initialPerasState,
  newRound,
  systemStart,
 )
import Peras.Prototype.Voting (voting)

data NodeState m = MkNodeState
  { self :: Party
  , clock :: SlotNumber
  , protocol :: PerasParams
  , stateVar :: TVar m PerasState
  , diffuserVar :: TVar m Diffuser
  }

defaultNodeState :: MonadSTM m => m (NodeState m)
defaultNodeState = initialNodeState nullTracer (mkParty 0 mempty mempty) systemStart def

initialNodeState :: MonadSTM m => Tracer m PerasLog -> Party -> SlotNumber -> PerasParams -> m (NodeState m)
initialNodeState tracer self clock protocol =
  do
    traceWith tracer $ Protocol protocol
    stateVar <- newTVarIO initialPerasState
    diffuserVar <- newTVarIO $ defaultDiffuser (perasΔ protocol)
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
  (newChains, newVotes) <- lift $ popChainsAndVotes diffuser s
  -- Operate node.
  lift $ tickNode tracer diffuser params party state s r payload newChains newVotes

tickNode ::
  forall m.
  MonadSTM m =>
  Tracer m PerasLog ->
  TVar m Diffuser ->
  PerasParams ->
  Party ->
  TVar m PerasState ->
  SlotNumber ->
  RoundNumber ->
  Payload ->
  [Chain] ->
  [Vote] ->
  m (PerasResult ())
tickNode tracer diffuser params party state s r payload newChains newVotes =
  -- 1. Get votes and chains from the network.
  runExceptT $ do
    -- 2. Invoke fetching.
    ExceptT $ fetching tracer params party state s newChains newVotes
    -- 3. Invoke voting if committee member.
    ExceptT $
      voting tracer params party state s (selectBlock tracer) (diffuseVote diffuser)
    -- 4. Invoke block creation if leader.
    ExceptT $ blockCreation tracer params party state s payload (diffuseChain diffuser)
