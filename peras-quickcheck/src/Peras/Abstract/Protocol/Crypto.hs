{-# LANGUAGE RecordWildCards #-}

module Peras.Abstract.Protocol.Crypto (
  CreateSignedBlock,
  createSignedBlock,
  CreateSignedCertificate,
  createSignedCertificate,
  CreateSignedVote,
  createSignedVote,
  CreateLeadershipProof,
  createLeadershipProof,
  CreateMembershipProof,
  createMembershipProof,
) where

import Data.Foldable (toList)
import Peras.Abstract.Protocol.Types (CreateLeadershipProof, CreateMembershipProof, CreateSignedBlock, CreateSignedCertificate, CreateSignedVote, CryptoError (..))
import Peras.Block (Block (..), Certificate (..), Party (..))
import Peras.Chain (Vote (..))
import Peras.Crypto (LeadershipProof (MkLeadershipProof), MembershipProof (MkMembershipProof), Signature (MkSignature))
import Prelude hiding (round)

import qualified Data.Hashable as H (Hashable (..))
import qualified Data.Serialize as Serialize (encode)
import qualified Data.Set as S (map)

createSignedBlock :: Applicative m => CreateSignedBlock m
createSignedBlock MkParty{pid = creatorId} slotNumber parentBlock certificate leadershipProof bodyHash =
  pure . pure $ MkBlock{..}
 where
  signature = sign (creatorId, slotNumber, parentBlock, certificate, leadershipProof, bodyHash)

createSignedCertificate :: Applicative m => CreateSignedCertificate m
createSignedCertificate _ round votes =
  pure $
    case toList $ blockHash `S.map` votes of
      [blockRef] -> pure MkCertificate{..}
      [] -> Left $ CertificationCreationFailed "Cannot create a certificate from no votes."
      _ -> Left $ CertificationCreationFailed "Cannot create a certificate from votes for different blocks."

createSignedVote :: Applicative m => CreateSignedVote m
createSignedVote MkParty{pid = creatorId} votingRound blockHash proofM votes =
  pure . pure $ MkVote{..}
 where
  signature = sign (creatorId, votingRound, blockHash, proofM, votes)

sign :: H.Hashable a => a -> Signature
sign = MkSignature . Serialize.encode . H.hash

createLeadershipProof :: Applicative m => CreateLeadershipProof m
createLeadershipProof = curry $ pure . pure . MkLeadershipProof . Serialize.encode . H.hash

createMembershipProof :: Applicative m => CreateMembershipProof m
createMembershipProof = curry $ pure . pure . MkMembershipProof . Serialize.encode . H.hash
