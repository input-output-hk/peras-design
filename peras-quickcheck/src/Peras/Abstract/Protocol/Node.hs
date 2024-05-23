{-# LANGUAGE FlexibleContexts #-}

module Peras.Abstract.Protocol.Node where

import Control.Arrow ((&&&))
import Control.Concurrent.Class.MonadSTM (MonadSTM (..))
import Control.Monad (when)
import Control.Monad.Except (ExceptT (ExceptT), runExceptT)
import Control.Monad.State (MonadState, gets, lift, modify')
import Peras.Abstract.Protocol.BlockCreation (blockCreation)
import Peras.Abstract.Protocol.Diffusion (Diffuser (..), diffuseChain, diffuseVote)
import Peras.Abstract.Protocol.Fetching (fetching)
import Peras.Abstract.Protocol.Preagreement (preagreement)
import Peras.Abstract.Protocol.Types (Payload, PerasParams (perasU), PerasResult, PerasState)
import Peras.Abstract.Protocol.Voting (voting)
import Peras.Block (Party)
import Peras.Numbering (SlotNumber)

data NodeState m = MkNodeState
  { self :: Party
  , clock :: SlotNumber
  , protocol :: PerasParams
  , stateVar :: TVar m PerasState
  , diffuserVar :: TVar m Diffuser
  }

tick :: (MonadSTM m, MonadState (NodeState m) m) => Payload -> m (PerasResult ())
tick payload =
  runExceptT $ do
    params <- gets protocol
    party <- gets self
    state <- gets stateVar
    diffuser <- gets diffuserVar
    -- 1. Increment clock.
    s <- gets $ (1 +) . clock
    modify' $ \node -> node{clock = s}
    let r = fromIntegral $ fromIntegral s `div` perasU params
        newRound = fromIntegral s `mod` perasU params == 0
    -- 2. Get votes and chains from the diffuser.
    (newChains, newVotes) <-
      lift . atomically $ do
        result <- (pendingChains &&& pendingVotes) <$> readTVar diffuser
        modifyTVar diffuser $ \d -> d{pendingChains = mempty, pendingVotes = mempty}
        pure result
    -- 3. Invoke fetching.
    ExceptT $ fetching params party state s newChains newVotes
    -- 4. Invoke block creation if leader.
    ExceptT $ blockCreation params party state s payload (diffuseChain diffuser)
    -- 5. Invoke voting if committee member.
    when newRound $
      ExceptT $
        voting params party state r preagreement (diffuseVote diffuser)
