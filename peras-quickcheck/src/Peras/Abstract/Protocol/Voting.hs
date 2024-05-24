{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.Abstract.Protocol.Voting where

import Prelude hiding (round)

import Control.Concurrent.Class.MonadSTM (MonadSTM (..))
import Control.Monad (when)
import Control.Monad.Except (ExceptT (..), runExceptT)
import Control.Monad.Trans (lift)
import Peras.Abstract.Protocol.Crypto (createMembershipProof, createSignedVote, isCommitteeMember)
import Peras.Abstract.Protocol.Types (PerasParams (..), PerasState (..), Voting)
import Peras.Block (Block (..), Certificate (..))
import Peras.Crypto (Hashable (..))
import Peras.Orphans ()

import qualified Data.Set as Set (insert, singleton)

voting :: MonadSTM m => Voting m
voting params@MkPerasParams{perasR, perasK} party perasState roundNumber preagreement diffuseVote = runExceptT $ do
  MkPerasState{..} <- lift $ readTVarIO perasState
  -- Invoke Preagreement(r) when in the first slot of r to get valid voting candidate B in slot rU + T .
  ExceptT (preagreement params party perasState roundNumber) >>= \case
    Nothing -> pure ()
    (Just (block, stake)) ->
      -- If party P is (voting) committee member in a round r,
      when (isCommitteeMember party roundNumber) $
        let
          -- (VR-1A) round(cert') = r − 1 and cert was received at least ∆ before the end of round r − 1,
          vr1a = round certPrime + 1 == roundNumber -- TODO: Check timestamp.
          -- (VR-1B) B extends the block certified by cert'
          vr1b = parentBlock block == blockRef certPrime -- TODO: Check extension.
          vr2a = round certPrime + fromIntegral perasR <= roundNumber
          vr2b =
            roundNumber > round certStar
              && fromIntegral (roundNumber - round certStar) `mod` perasK == 0
         in
          when (vr1a && vr1b || vr2a && vr2b) $
            do
              proofM <- ExceptT $ createMembershipProof roundNumber (Set.singleton party)
              -- and σ is a signature on the rest of v.
              -- then create a vote v = (r, P, h, π, σ), where
              -- h is the hash of B,
              -- π is the slot-leadership proof,
              vote <- ExceptT $ createSignedVote party roundNumber (hash block) proofM stake
              -- Add v to V and diffuse it.
              lift $ atomically $ modifyTVar' perasState $ \s -> s{votes = vote `Set.insert` votes}
              ExceptT $ diffuseVote vote
