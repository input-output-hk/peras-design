{-# LANGUAGE FlexibleContexts #-}

module Peras.Abstract.Protocol.Node where

import Control.Concurrent.Class.MonadSTM (MonadSTM (..))
import Control.Monad.State
import Peras.Abstract.Protocol.Diffusion
import Peras.Abstract.Protocol.Types
import Peras.Block
import Peras.Numbering

data NodeState m = MkNodeState
  { protocol :: PerasParams
  , peras :: TVar m PerasState
  , clock :: SlotNumber
  , diffuser :: TVar m Diffuser
  , self :: Party
  }

tick :: (MonadSTM m, MonadState (NodeState m) m) => m (PerasResult ())
tick =
  do
    s <- gets $ (1 +) . clock
    -- 1. Increment clock.
    modify' $ \node -> node{clock = s}
    -- 2. Get votes and chains from the diffuser.
    -- 3. Invoke fetching.
    -- 4. Invoke block creation if leader.
    -- 5. Invoke voting if committee member.
    undefined
