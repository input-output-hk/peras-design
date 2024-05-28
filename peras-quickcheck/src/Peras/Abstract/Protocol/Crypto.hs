{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Peras.Abstract.Protocol.Crypto where

import Prelude hiding (round)

import Control.Monad.Except (throwError)
import Data.Foldable (toList)
import Peras.Abstract.Protocol.Types (Payload, PerasError (..), PerasResult, VotingWeight)
import Peras.Block (Block (..), Certificate (..), Party (..), PartyId)
import Peras.Chain (Vote (..))
import Peras.Crypto (Hash (..), Hashable (..), LeadershipProof (MkLeadershipProof), MembershipProof (MkMembershipProof), Signature (MkSignature), VerificationKey (MkVerificationKey))
import Peras.Numbering

import qualified Data.Hashable as H (Hashable (..))
import qualified Data.Serialize as Serialize (decode, encode)
import Data.Set (Set)
import qualified Data.Set as S (map)

createSignedBlock ::
  Applicative m =>
  Party ->
  SlotNumber ->
  Hash Block ->
  Maybe Certificate ->
  LeadershipProof ->
  Hash Payload ->
  m (PerasResult Block)
createSignedBlock MkParty{pid = creatorId} slotNumber parentBlock certificate leadershipProof bodyHash =
  pure . pure $ MkBlock{..}
 where
  signature = sign (creatorId, slotNumber, parentBlock, certificate, leadershipProof, bodyHash)

createSignedCertificate :: Applicative m => Party -> Set Vote -> m (PerasResult Certificate)
createSignedCertificate _ votes =
  pure $
    case toList $ S.map (\MkVote{votingRound, blockHash} -> (votingRound, blockHash)) votes of
      [(round, blockRef)] -> pure MkCertificate{..}
      [] -> throwError $ CertificationCreationFailed "Cannot create a certificate from no votes."
      _ -> throwError $ CertificationCreationFailed "Cannot create a certificate from votes for different blocks."

createSignedVote ::
  Applicative m =>
  Party ->
  RoundNumber ->
  Hash Block ->
  MembershipProof ->
  VotingWeight ->
  m (PerasResult Vote)
createSignedVote MkParty{pid = creatorId} votingRound blockHash proofM votes =
  pure . pure $ MkVote{..}
 where
  signature = sign (creatorId, votingRound, blockHash, proofM, votes)

sign :: H.Hashable a => a -> Signature
sign = MkSignature . Serialize.encode . H.hash

createLeadershipProof ::
  Applicative m =>
  SlotNumber ->
  Set Party ->
  m (PerasResult LeadershipProof)
createLeadershipProof = curry $ pure . pure . MkLeadershipProof . Serialize.encode . H.hash

createMembershipProof ::
  Applicative m =>
  RoundNumber ->
  Set Party ->
  m (PerasResult MembershipProof)
createMembershipProof = curry $ pure . pure . MkMembershipProof . Serialize.encode . H.hash

instance Hashable [()] where
  hash _ = MkHash mempty

-- FIXME: Replace with proper leadership and membership proofs.

mkParty :: PartyId -> [SlotNumber] -> [RoundNumber] -> Party
mkParty ident leadershipSlots membershipRounds =
  MkParty ident . MkVerificationKey $
    Serialize.encode (getSlotNumber <$> leadershipSlots, getRoundNumber <$> membershipRounds)

isSlotLeader :: Party -> SlotNumber -> Bool
isSlotLeader MkParty{pkey = MkVerificationKey key} (MkSlotNumber s) =
  either
    (const False)
    (slotIsLeader . fst)
    (Serialize.decode key :: Either String ([Integer], [Integer]))
 where
  slotIsLeader :: [Integer] -> Bool
  slotIsLeader = elem s

isCommitteeMember :: Party -> RoundNumber -> Bool
isCommitteeMember MkParty{pkey = MkVerificationKey key} (MkRoundNumber r) =
  either
    (const False)
    (roundIsCommitteeMember . snd)
    (Serialize.decode key :: Either String ([Integer], [Integer]))
 where
  roundIsCommitteeMember :: [Integer] -> Bool
  roundIsCommitteeMember = elem r
