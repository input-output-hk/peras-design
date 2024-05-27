{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Simulate the network environment for a single node.
module Peras.Abstract.Protocol.Network where

import Control.Concurrent.Class.MonadSTM (MonadSTM (modifyTVar'), atomically, readTVarIO)
import Control.Monad.Class.MonadTimer (MonadDelay)
import Control.Monad.State (execStateT, gets)
import Control.Monad.Trans (lift)
import Control.Tracer (Tracer)
import Data.Functor (void)
import qualified Data.Set as Set
import Peras.Abstract.Protocol.Crypto (mkParty)
import Peras.Abstract.Protocol.Diffusion (Diffuser (..))
import Peras.Abstract.Protocol.Node (NodeState (..), initialNodeState, stateVar, tick)
import Peras.Abstract.Protocol.Trace (PerasLog)
import Peras.Abstract.Protocol.Types (PerasState)
import Peras.Numbering (SlotNumber)

runNetwork :: forall m. (MonadSTM m, MonadDelay m) => Tracer m PerasLog -> (SlotNumber -> m Diffuser) -> m PerasState
runNetwork tracer scenario = do
  let voteEvery10Rounds = mkParty 42 [] [10]
  initial <- initialNodeState voteEvery10Rounds 1
  execStateT (loop 0) initial >>= \MkNodeState{stateVar} -> readTVarIO stateVar
 where
  loop slot = do
    -- 1. feed the diffuser with incoming chains and votes
    MkDiffuser{pendingChains = newChains, pendingVotes = newVotes} <- lift $ scenario slot
    diffuser <- gets diffuserVar
    lift $
      atomically $
        modifyTVar'
          diffuser
          ( \MkDiffuser{pendingChains, pendingVotes} ->
              MkDiffuser
                { pendingChains = pendingChains `Set.union` newChains
                , pendingVotes = pendingVotes `Set.union` newVotes
                }
          )
    -- 2. Tick the node.
    void $ tick tracer []
    -- 3. drain diffuser from possible votes and blocks emitted by the node.
    loop (slot + 1)
