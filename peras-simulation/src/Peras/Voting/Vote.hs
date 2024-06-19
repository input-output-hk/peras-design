{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}

module Peras.Voting.Vote where

import Cardano.Crypto.DSIGN (Ed25519DSIGN)
import Cardano.Crypto.Hash (Blake2b_256, Hash)
import qualified Cardano.Crypto.Hash as Hash
import qualified Cardano.Crypto.KES as KES
import qualified Cardano.Crypto.VRF.Class as VRF
import qualified Cardano.Crypto.VRF.Praos as VRF
import Cardano.Ledger.NonIntegral (CompareResult (..), taylorExpCmp)
import qualified Data.ByteString.Builder as BS
import qualified Data.ByteString.Lazy as LBS
import Data.Data (Proxy (..))
import Data.Ratio ((%))
import Data.Word (Word64)
import Numeric.Natural (Natural)
import Statistics.Distribution (cumulative)
import Statistics.Distribution.Binomial (binomial)

data Vote block = MkVote
  { creatorId :: PartyId
  , votingRound :: RoundNumber
  , blockHash :: block
  , membershipProof :: MembershipProof
  , votingWeight :: VotingWeight
  , signature :: Signature
  }

newtype VotingWeight = VotingWeight {unVotingWeight :: Word64}
  deriving stock (Eq, Ord, Show)
  deriving newtype (Num, Integral, Real, Enum)

-- | A party (SPO) is identified by its pool ID which is the hash of its VRF verification key.
newtype PartyId = MkPartyId {unPartyId :: Hash Blake2b_256 (VRF.VerKeyVRF VRF.PraosVRF)}
  deriving stock (Eq, Ord, Show)

-- | A round number is just a natural number.
newtype RoundNumber = RoundNumber {unRoundNumber :: Word64}
  deriving stock (Eq, Ord, Show)

type MembershipProof = VRF.CertifiedVRF VRF.PraosVRF MembershipInput

type Signature = KES.SignedKES (KES.Sum6KES Ed25519DSIGN Blake2b_256) MembershipProof

-- | The input to the `evalVRF` is a hash value.
data MembershipInput = MkMembershipInput {unNonce :: Hash Blake2b_256 MembershipInput}
  deriving (Eq, Ord, Show)

data Voter = MkVoter
  { voterId :: PartyId
  , voterStake :: Integer
  , vrfSignKey :: VRF.SignKeyVRF VRF.PraosVRF
  , kesPeriod :: KES.Period
  , kesSignKey :: KES.SignKeyKES (KES.Sum6KES Ed25519DSIGN Blake2b_256)
  }

newtype CommitteeSize = CommitteeSize Integer
  deriving (Eq, Show)

castVote :: a -> Integer -> MembershipInput -> CommitteeSize -> RoundNumber -> Voter -> Maybe (Vote a)
castVote blockHash totalStake (MkMembershipInput h) (CommitteeSize committeeSize) roundNumber@RoundNumber{unRoundNumber} MkVoter{..} =
  undefined -- let nonce = MkMembershipInput . Hash.castHash . Hash.hashWith id $ Hash.hashToBytes h <> "peras" <> LBS.toStrict (BS.toLazyByteString (BS.word64BE unRoundNumber))
  --     certVRF = VRF.evalCertified @_ @MembershipInput () nonce vrfSignKey
  --     certKES = KES.signedKES () kesPeriod certVRF kesSignKey
  --     ratio = toInteger nonce % toInteger (2 ^ (8 * VRF.sizeOutputVRF (Proxy @VRF.PraosVRF)))
  --  in case selectVote committeeSize ratio voterStake totalStake of
  --       0 -> Nothing
  --       n ->
  --         Just
  --           MkVote
  --             { creatorId = voterId
  --             , votingRound = roundNumber
  --             , blockHash
  --             , membershipProof = certVRF
  --             , votingWeight = n
  --             , signature = certKES
  --             }

-- stolen from https://github.com/algorand/sortition/blob/main/sortition.cpp
selectVote ::
  -- | Expected committee size
  Integer ->
  -- | Outcome of "random" function, used to find voter's resulting weight
  Rational ->
  -- | Voter's stake
  Integer ->
  -- | Total stake
  Integer ->
  VotingWeight
selectVote expectedSize ratio voterStake totalStake =
  go 0
 where
  n = voterStake
  p = expectedSize % totalStake
  ρ = fromRational ratio
  coin = fromIntegral voterStake
  cdf = binomial (fromIntegral n) (fromRational p)
  go k =
    if
      | cumulative cdf k >= ρ -> VotingWeight (floor k)
      | k >= coin -> VotingWeight (fromInteger voterStake)
      | otherwise -> go (k + 1)
