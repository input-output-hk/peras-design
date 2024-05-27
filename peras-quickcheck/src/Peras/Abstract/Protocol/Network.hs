{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Simulate the network environment for a single node.
module Peras.Abstract.Protocol.Network where

import Control.Concurrent.Class.MonadSTM (MonadSTM (modifyTVar'), atomically, readTVarIO, writeTVar)
import Control.Monad.Class.MonadTimer (MonadDelay)
import Control.Monad.State (execStateT, gets)
import Control.Monad.Trans (lift)
import Control.Tracer (Tracer)
import Data.Functor (void)
import qualified Data.Set as Set
import Peras.Abstract.Protocol.Crypto (mkParty)
import Peras.Abstract.Protocol.Diffusion (Diffuser (..), defaultDiffuser)
import Peras.Abstract.Protocol.Node (NodeState (..), initialNodeState, stateVar, tick)
import Peras.Abstract.Protocol.Trace (PerasLog)
import Peras.Abstract.Protocol.Types (PerasState)
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
