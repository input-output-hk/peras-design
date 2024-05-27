{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}

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
import Peras.Abstract.Protocol.Types (Payload, PerasParams (perasU), PerasResult, PerasState, defaultParams, initialPerasState)
import Peras.Abstract.Protocol.Voting (voting)
import Peras.Block (Party)
import Peras.Chain (Chain, Vote)
import Peras.Numbering (SlotNumber)

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

tick :: MonadSTM m => Tracer m PerasLog -> Payload -> StateT (NodeState m) m (PerasResult ())
tick tracer payload = do
  params <- gets protocol
  party <- gets self
  state <- gets stateVar
  diffuser <- gets diffuserVar
  -- 1. Increment clock.
  s <- gets $ (1 +) . clock
  lift $ traceWith tracer $ Tick s
  modify' $ \node -> node{clock = s}
  let r = fromIntegral $ fromIntegral s `div` perasU params
      newRound = fromIntegral s `mod` perasU params == 0
  -- 2. Get votes and chains from the network.
  (newChains, newVotes) <- lift (fetchNewChainsAndVotes diffuser)
  runExceptT $ do
    -- 3. Invoke fetching.
    ExceptT $ lift $ fetching params party state s newChains newVotes
    -- 4. Invoke block creation if leader.
    ExceptT $ lift $ blockCreation params party state s payload (diffuseChain diffuser)
    -- 5. Invoke voting if committee member.
    when newRound $
      ExceptT $
        lift $
          voting params party state r preagreement (diffuseVote diffuser)

fetchNewChainsAndVotes :: MonadSTM m => TVar m Diffuser -> m (Set Chain, Set Vote)
fetchNewChainsAndVotes diffuser = atomically $ do
  result <- (pendingChains &&& pendingVotes) <$> readTVar diffuser
  modifyTVar diffuser $ \d -> d{pendingChains = mempty, pendingVotes = mempty}
  pure result
