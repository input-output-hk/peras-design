{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.Abstract.Protocol.Voting where

import Prelude hiding (round)

import Control.Concurrent.Class.MonadSTM (MonadSTM (..))
import Control.Monad (when)
import Control.Monad.Except (ExceptT (..), runExceptT)
import Control.Monad.Trans (lift)
import Data.Foldable (toList)
import Peras.Abstract.Protocol.Crypto (createMembershipProof, createSignedVote, isCommitteeMember)
import Peras.Abstract.Protocol.Types (DiffuseVote, PerasParams (..), PerasResult, PerasState (..), Preagreement)
import Peras.Block (Block (..), Certificate (..), Party (pid))
import Peras.Chain (Chain)
import Peras.Crypto (Hash, Hashable (..))
import Peras.Numbering (RoundNumber, SlotNumber)
import Peras.Orphans ()

import Control.Tracer (Tracer, traceWith)
import qualified Data.Set as Set (insert, singleton)
import Peras.Abstract.Protocol.Trace (PerasLog (..))

voting ::
  MonadSTM m =>
  Tracer m PerasLog ->
  PerasParams ->
  Party ->
  TVar m PerasState ->
  RoundNumber ->
  Preagreement m ->
  DiffuseVote m ->
  m (PerasResult ())
voting tracer params@MkPerasParams{perasR, perasK} party perasState roundNumber preagreement diffuseVote = runExceptT $ do
  MkPerasState{..} <- lift $ readTVarIO perasState
  -- Invoke Preagreement(r) when in the first slot of r to get valid voting candidate B in slot rU + T .
  ExceptT (preagreement params party perasState roundNumber) >>= \case
    Nothing -> pure ()
    Just (block, stake) ->
      -- If party P is (voting) committee member in a round r,
      when (isCommitteeMember party roundNumber) $ do
        let
          -- (VR-1A) round(cert') = r − 1 and cert was received at least ∆ before the end of round r − 1,
          vr1a = round certPrime + 1 == roundNumber -- TODO: Check timestamp.
          -- (VR-1B) B extends the block certified by cert'
          vr1b = extends block certPrime $ toList chains
          vr2a = round certPrime + fromIntegral perasR <= roundNumber
          vr2b =
            roundNumber > round certStar
              && fromIntegral (roundNumber - round certStar) `mod` perasK == 0
        lift $ traceWith tracer $ VotingLogic (pid party) vr1a vr1b vr2a vr2b
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
            lift $ traceWith tracer $ CastVote (pid party) vote

extends :: Block -> Certificate -> [Chain] -> Bool
extends block cert = any chainExtends
 where
  dropUntilBlock :: SlotNumber -> Hash Block -> [Block] -> [Block]
  dropUntilBlock slotHint target blocks =
    let candidates = dropWhile (\block' -> slotHint < slotNumber block') blocks
     in case candidates of
          [] -> []
          (candidate : _) -> if target == hash candidate then candidates else []
  chainExtends :: Chain -> Bool
  chainExtends =
    any (\block' -> parentBlock block' == blockRef cert)
      . dropUntilBlock (slotNumber block) (hash block)
