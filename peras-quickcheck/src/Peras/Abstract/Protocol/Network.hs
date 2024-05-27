{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Simulate the network environment for a single node.
module Peras.Abstract.Protocol.Network where

import Control.Concurrent.Class.MonadSTM (MonadSTM, readTVarIO)
import Control.Monad.Class.MonadTimer (MonadDelay, threadDelay)
import Control.Monad.State (execStateT, runStateT)
import Control.Monad.Trans (lift)
import Data.Functor (void)
import Peras.Abstract.Protocol.Crypto (mkParty)
import Peras.Abstract.Protocol.Node (NodeState (MkNodeState), initialNodeState, stateVar, tick)
import Peras.Abstract.Protocol.Types (PerasState)

runNetwork :: forall m. (MonadSTM m, MonadDelay m) => m PerasState
runNetwork = do
  let voteEvery10Rounds = mkParty 42 [] [10]
  initial <- initialNodeState voteEvery10Rounds 1
  execStateT loop initial >>= \MkNodeState{stateVar} -> readTVarIO stateVar
 where
  slotDuration = 1000000

  loop = do
    -- 0. feed the diffuser with incoming chains and votes
    -- 1. Tick the node.
    void $ tick []
    -- 2. drain diffuser from possible votes and blocks emitted by the node.
    lift $ threadDelay slotDuration
    loop
