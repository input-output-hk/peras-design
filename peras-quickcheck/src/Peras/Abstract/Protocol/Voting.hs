{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.Abstract.Protocol.Voting where

import Prelude hiding (round)

import Control.Applicative ((<|>))
import Control.Concurrent.Class.MonadSTM (MonadSTM (..))
import Control.Monad (when)
import Control.Monad.Except (ExceptT (..), runExcept, runExceptT, throwError)
import Control.Monad.Trans (lift)
import qualified Data.Set as Set
import Peras.Abstract.Protocol.Crypto (createMembershipProof, createSignedVote)
import Peras.Abstract.Protocol.Types (PerasError (..), PerasParams (..), PerasState (..), Voting)
import Peras.Block (Block (..), Certificate (..), Party (..))
import Peras.Crypto (Hashable (..))
import Peras.Numbering (RoundNumber)
import Peras.Orphans ()

voting :: MonadSTM m => Voting m
voting params@MkPerasParams{perasR} party perasState roundNumber preagreement diffuseVote = runExceptT $ do
  MkPerasState{..} <- lift $ readTVarIO perasState
  -- Invoke Preagreement(r) when in the first slot of r to get valid voting candidate B in slot rU + T .
  ExceptT (preagreement params party perasState roundNumber) >>= \case
    Nothing -> pure ()
    (Just (block, stake)) -> do
      -- If party P is (voting) committee member in a round r,
      if isCommitteeMember party roundNumber
        then do
          -- (VR-1A) round(cert') = r − 1 and cert was received at least ∆ before the end of round r − 1,
          if (round certPrime /= roundNumber - 1)
            ||
            -- (VR-1B) B extends the block certified by cert'
            -- TODO: check extension longer than 1 block
            (parentBlock block /= blockRef certPrime)
            then throwError $ NoVoting
            else -- (VR-2A) r ≥ round(cert ) + R

              if (round certStar + fromIntegral perasR > roundNumber)
                then throwError $ NoVoting
                else pure ()

          -- then create a vote v = (r, P, h, π, σ), where
          -- h is the hash of B,
          -- π is the slot-leadership proof,
          proofM <- ExceptT $ createMembershipProof roundNumber (Set.singleton party)
          -- and σ is a signature on the rest of v.
          vote <- ExceptT $ createSignedVote party roundNumber (hash block) proofM stake
          -- Add v to V and diffuse it.
          lift $ atomically $ modifyTVar' perasState $ \s -> s{votes = vote `Set.insert` votes}
          ExceptT $ diffuseVote vote
        else pure ()

isCommitteeMember :: Party -> RoundNumber -> Bool
isCommitteeMember MkParty{pid} roundNumber =
  pid == fromIntegral roundNumber
