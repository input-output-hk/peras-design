{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.Abstract.Protocol.Voting where

import Control.Concurrent.Class.MonadSTM (MonadSTM (..))
import Control.Monad.Except (ExceptT (..), runExceptT)
import Control.Monad.Trans (lift)
import qualified Data.Set as Set
import Peras.Abstract.Protocol.BytesModulo (modulo)
import Peras.Abstract.Protocol.Crypto (createMembershipProof, createSignedVote)
import Peras.Abstract.Protocol.Types (PerasState (..), Voting)
import Peras.Block (Party (..))
import Peras.Crypto (Hashable (..), VerificationKey (MkVerificationKey))
import Peras.Numbering (RoundNumber)
import Peras.Orphans ()

voting :: MonadSTM m => Voting m
voting params party perasState roundNumber preagreement diffuseVote = runExceptT $ do
  MkPerasState{..} <- lift $ readTVarIO perasState
  -- Invoke Preagreement(r) when in the first slot of r to get valid voting candidate B in slot rU + T .
  ExceptT (preagreement params party perasState roundNumber) >>= \case
    Nothing -> pure ()
    (Just (block, stake)) -> do
      -- If party P is (voting) committee member in a round r,
      if isCommitteeMember party roundNumber
        then pure ()
        else do
          proofM <- ExceptT $ createMembershipProof roundNumber (Set.singleton party)
          -- then create a vote v = (r, P, h, π, σ), where
          -- h is the hash of B,
          -- π is the slot-leadership proof,
          -- and σ is a signature on the rest of v.
          vote <- ExceptT $ createSignedVote party roundNumber (hash block) proofM stake
          -- Add v to V and diffuse it.
          lift $ atomically $ modifyTVar' perasState $ \s -> s{votes = vote `Set.insert` votes}
          ExceptT $ diffuseVote vote
          pure ()

isCommitteeMember :: Party -> RoundNumber -> Bool
isCommitteeMember MkParty{pkey = MkVerificationKey bytes} roundNumber =
  bytes `modulo` fromIntegral roundNumber == 0
