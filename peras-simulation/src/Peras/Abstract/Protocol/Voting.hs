{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.Abstract.Protocol.Voting where

import Prelude hiding (round)

import Control.Concurrent.Class.MonadSTM (MonadSTM (..))
import Control.Monad (when)
import Control.Monad.Except (ExceptT (..), runExceptT)
import Control.Monad.Trans (lift)
import Control.Tracer (Tracer, traceWith)
import Data.Foldable (toList)
import qualified Data.Map as Map (lookup)
import qualified Data.Set as Set (insert, singleton)
import Peras.Abstract.Protocol.Crypto (createMembershipProof, createSignedVote, isCommitteeMember)
import Peras.Abstract.Protocol.Trace (PerasLog (..))
import Peras.Abstract.Protocol.Types (DiffuseVote, PerasParams (..), PerasResult, PerasState (..), Preagreement, genesisCert)
import Peras.Block (Block (..), Certificate (..), Party (pid))
import Peras.Chain (Chain)
import Peras.Crypto (Hashable (..))
import Peras.Numbering (RoundNumber)
import Peras.Orphans ()

-- Party P does the following at the beginning of each voting round r:
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
voting tracer params@MkPerasParams{perasR, perasK, perasU, perasΔ} party perasState roundNumber preagreement diffuseVote =
  runExceptT $ do
    MkPerasState{..} <- lift $ readTVarIO perasState
    -- 1. Invoke Preagreement(r) when in the first slot of r to get valid voting candidate B in slot r U + T.
    ExceptT (preagreement params party perasState roundNumber) >>= \case
      Nothing -> pure ()
      Just (block, stake) ->
        -- 2. If party P is (voting) committee member in a round r,
        when (isCommitteeMember party roundNumber) $ do
          let
            -- (VR-1A) round(cert') = r − 1 and cert' was received at least ∆ before the end of round r − 1, and
            oldEnough s = fromIntegral s + perasΔ <= fromIntegral (roundNumber - 1) * perasU + perasU - 1
            vr1a =
              round certPrime + 1 == roundNumber
                && maybe True {- Only the genesis certificate is not in the map. -} oldEnough (Map.lookup certPrime certs)
            -- (VR-1B) B extends the block certified by cert', or
            vr1b = extends block certPrime $ toList chains
            -- (VR-2A) r >= round(cert') + R,
            vr2a = roundNumber >= round certPrime + fromIntegral perasR
            -- (VR-2B) r = round(cert*) + c K for some c > 0, and
            vr2b =
              roundNumber > round certStar -- eliminates c = 0
                && fromIntegral roundNumber `mod` perasK == fromIntegral (round certStar) `mod` perasK -- some muliple of K
          lift $ traceWith tracer $ VotingLogic (pid party) vr1a vr1b vr2a vr2b
          -- then create a vote v = (r, P, h, π, σ)
          when (vr1a && vr1b || vr2a && vr2b) $
            do
              proofM <- ExceptT $ createMembershipProof roundNumber (Set.singleton party)
              -- h is the hash of B,
              -- π is the committee-membership proof,
              -- and σ is a signature on the rest of v.
              vote <- ExceptT $ createSignedVote party roundNumber (hash block) proofM stake
              -- Add v to V and diffuse it.
              lift $ atomically $ modifyTVar' perasState $ \s -> s{votes = vote `Set.insert` votes}
              ExceptT $ diffuseVote (fromIntegral $ fromIntegral roundNumber * perasU) vote
              lift $ traceWith tracer $ CastVote (pid party) vote

-- | Check whether a block extends the block certified in a certificate.
-- Note that the `extends` relationship is transitive ''and'' reflexive.
extends :: Block -> Certificate -> [Chain] -> Bool
extends block cert chain
  | cert == genesisCert = True -- All blocks extend genesis.
  | otherwise = any chainExtends chain
 where
  chainExtends :: Chain -> Bool
  chainExtends =
    any ((== blockRef cert) . hash) -- Is the certified block on the chain?
      . dropWhile ((/= hash block) . hash) -- Truncate the chain to the block in question.
