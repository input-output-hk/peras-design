{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.Abstract.Protocol.Crypto where

import Control.Monad.Except (throwError)
import Data.Foldable (toList)
import Peras.Abstract.Protocol.Types (CreateLeadershipProof, CreateMembershipProof, CreateSignedBlock, CreateSignedCertificate, CreateSignedVote, PerasError (..), VotingWeight)
import Peras.Block (Block (..), Certificate (..), Party (..))
import Peras.Chain (Vote (..))
import Peras.Crypto (Hash (..), Hashable (..), LeadershipProof (MkLeadershipProof), MembershipProof (MkMembershipProof), Signature (MkSignature))
import Prelude hiding (round)

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.Hashable as H (Hashable (..))
import qualified Data.Serialize as Serialize (encode)
import qualified Data.Set as S (map)
import System.Random (mkStdGen, uniformR)

createSignedBlock :: Applicative m => CreateSignedBlock m
createSignedBlock MkParty{pid = creatorId} slotNumber parentBlock certificate leadershipProof bodyHash =
  pure . pure $ MkBlock{..}
 where
  signature = sign (creatorId, slotNumber, parentBlock, certificate, leadershipProof, bodyHash)

createSignedCertificate :: Applicative m => CreateSignedCertificate m
createSignedCertificate _ votes =
  pure $
    case toList $ S.map (\MkVote{votingRound, blockHash} -> (votingRound, blockHash)) votes of
      [(round, blockRef)] -> pure MkCertificate{..}
      [] -> throwError $ CertificationCreationFailed "Cannot create a certificate from no votes."
      _ -> throwError $ CertificationCreationFailed "Cannot create a certificate from votes for different blocks."

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

instance Hashable [()] where
  hash _ = MkHash mempty
