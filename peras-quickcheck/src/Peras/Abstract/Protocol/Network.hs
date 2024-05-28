{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Simulate the network environment for a single node.
module Peras.Abstract.Protocol.Network where

import Control.Arrow ((&&&))
import Control.Concurrent.Class.MonadSTM (MonadSTM (TVar, modifyTVar'), atomically, newTVarIO, readTVarIO, writeTVar)
import Control.Monad (forM)
import Control.Monad.Class.MonadTimer (MonadDelay)
import Control.Monad.State (StateT, execStateT, gets, modify')
import Control.Monad.Trans (lift)
import Control.Tracer (Tracer, traceWith)
import Data.Foldable (toList)
import Data.Functor (void)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Peras.Abstract.Protocol.Crypto (mkParty)
import Peras.Abstract.Protocol.Diffusion (Diffuser (..), defaultDiffuser)
import Peras.Abstract.Protocol.Node (NodeState (MkNodeState, clock, diffuserVar, stateVar), initialNodeState, tick, tickNode)
import Peras.Abstract.Protocol.Trace (PerasLog (..))
import Peras.Abstract.Protocol.Types (Payload, PerasParams, PerasResult, PerasState, defaultParams, inRound, initialPerasState)
import Peras.Block (Party)
import Peras.Numbering (SlotNumber)

runNetwork :: forall m. (MonadSTM m, MonadDelay m) => Tracer m PerasLog -> (SlotNumber -> m Diffuser) -> m PerasState
runNetwork tracer scenario = do
  let voteEvery10Rounds = mkParty 42 [] [10]
  initial <- initialNodeState voteEvery10Rounds 0
  execStateT loop initial >>= \MkNodeState{stateVar} -> readTVarIO stateVar
 where
  loop = do
    -- 1. feed the diffuser with incoming chains and votes
    slot <- gets clock
    diffuser <- gets diffuserVar
    updateIncomingFromScenario diffuser slot
    -- 2. Tick the node triggering fetching, block creation, and voting processes
    void $ tick tracer []
    -- 3. drain diffuser from possible votes and blocks emitted by the node.
    lift $ atomically $ writeTVar diffuser defaultDiffuser
    loop

  updateIncomingFromScenario diffuser slot = lift $ do
    MkDiffuser{pendingChains = newChains, pendingVotes = newVotes} <- scenario slot
    atomically $ modifyTVar' diffuser $ \pending ->
      pending
        { pendingChains = Set.union newChains $ pendingChains pending
        , pendingVotes = Set.union newVotes $ pendingVotes pending
        }

data Network m = MkNetwork
  { netClock :: SlotNumber
  , protocol :: PerasParams
  , stateVars :: Map Party (TVar m PerasState)
  , netDiffuserVar :: TVar m Diffuser
  }

initialNetwork :: MonadSTM m => Set Party -> SlotNumber -> m (Network m)
initialNetwork parties netClock =
  do
    let protocol = defaultParams
    stateVars <- Map.fromList <$> mapM ((<$> newTVarIO initialPerasState) . (,)) (toList parties)
    netDiffuserVar <- newTVarIO defaultDiffuser
    pure MkNetwork{..}

tickNetwork :: forall m. MonadSTM m => Tracer m PerasLog -> Payload -> StateT (Network m) m (PerasResult ())
tickNetwork tracer payload = do
  params <- gets protocol
  states <- gets stateVars
  diffuser <- gets netDiffuserVar
  -- Increment clock.
  s <- gets $ (1 +) . netClock
  modify' $ \net -> net{netClock = s}
  let r = inRound s params
  lift $ traceWith tracer $ Tick s r
  -- Retrieve chains and votes to be diffused.
  (newChains, newVotes) <- lift $ (pendingChains &&& pendingVotes) <$> readTVarIO diffuser
  lift . atomically . modifyTVar' diffuser $ \d -> d{pendingChains = mempty, pendingVotes = mempty}
  -- Operate nodes.
  fmap sequence_ . forM (Map.toList states) $ \(party, state) ->
    lift $ tickNode tracer params party state s r payload newChains newVotes diffuser
