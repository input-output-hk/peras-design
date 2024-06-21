{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Peras.Voting.Vote where

import Cardano.Crypto.DSIGN (Ed25519DSIGN)
import Cardano.Crypto.Hash (Blake2b_256, Hash)
import qualified Cardano.Crypto.Hash as Hash
import qualified Cardano.Crypto.KES as KES
import Cardano.Crypto.KES.Class (genKeyKES)
import Cardano.Crypto.Seed (mkSeedFromBytes)
import Cardano.Crypto.Util (SignableRepresentation (..))
import qualified Cardano.Crypto.VRF.Class as VRF
import qualified Cardano.Crypto.VRF.Praos as VRF
import Control.DeepSeq (NFData)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Builder as BS
import qualified Data.ByteString.Lazy as LBS
import Data.Either (isRight)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Ratio ((%))
import Data.Serialize (getWord64le, runGet)
import Data.Word (Word64)
import GHC.Generics (Generic)
import Statistics.Distribution (cumulative)
import Statistics.Distribution.Binomial (binomial)

data Vote block = MkVote
  { creatorId :: PartyId
  , votingRound :: RoundNumber
  , blockHash :: block
  , membershipProof :: MembershipProof
  , votingWeight :: VotingWeight
  , sigKesPeriod :: KES.Period
  , signature :: Signature
  }
  deriving stock (Show, Generic)
  deriving anyclass (NFData)

newtype VotingWeight = VotingWeight {unVotingWeight :: Word64}
  deriving stock (Eq, Ord, Show)
  deriving newtype (Num, Integral, Real, Enum, NFData)

-- | A party (SPO) is identified by its pool ID which is the hash of its VRF verification key.
newtype PartyId = MkPartyId {unPartyId :: Hash Blake2b_256 (VRF.VerKeyVRF VRF.PraosVRF)}
  deriving stock (Eq, Ord, Show)
  deriving newtype (NFData)

mkPartyId :: BS.ByteString -> PartyId
mkPartyId = MkPartyId . fromJust . Hash.hashFromBytes

-- | A round number is just a natural number.
newtype RoundNumber = RoundNumber {unRoundNumber :: Word64}
  deriving newtype (Eq, Ord, Show, Num, Integral, Real, Enum, NFData)

type MembershipProof = VRF.CertifiedVRF VRF.PraosVRF MembershipInput

deriving anyclass instance NFData (VRF.CertifiedVRF VRF.PraosVRF MembershipInput)

type Signature = KES.SigKES (KES.Sum6KES Ed25519DSIGN Blake2b_256)

-- | The input to the `evalVRF` is a hash value.
newtype MembershipInput = MkMembershipInput {unNonce :: Hash Blake2b_256 MembershipInput}
  deriving newtype (Eq, Ord, Show, NFData)

fromBytes :: BS.ByteString -> MembershipInput
fromBytes = MkMembershipInput . fromJust . Hash.hashFromBytes

mkNonce :: Hash h a -> Word64 -> MembershipInput
mkNonce h unRoundNumber = MkMembershipInput . Hash.castHash . Hash.hashWith id $ Hash.hashToBytes h <> "peras" <> LBS.toStrict (BS.toLazyByteString (BS.word64BE unRoundNumber))

data Voter = MkVoter
  { voterId :: PartyId
  , voterStake :: Integer
  , vrfSignKey :: VRF.SignKeyVRF VRF.PraosVRF
  , vrfVerKey :: VRF.VerKeyVRF VRF.PraosVRF
  , kesPeriod :: KES.Period
  , kesSignKey :: KES.SignKeyKES (KES.Sum6KES Ed25519DSIGN Blake2b_256)
  , kesVerKey :: KES.VerKeyKES (KES.Sum6KES Ed25519DSIGN Blake2b_256)
  }
  deriving stock (Show, Generic)
  deriving anyclass (NFData)

newVRFSigningKey :: BS.ByteString -> (VRF.SignKeyVRF VRF.PraosVRF, VRF.VerKeyVRF VRF.PraosVRF)
newVRFSigningKey = VRF.genKeyPairVRF . mkSeedFromBytes

newKESSigningKey :: BS.ByteString -> KES.SignKeyKES (KES.Sum6KES Ed25519DSIGN Blake2b_256)
newKESSigningKey = genKeyKES . mkSeedFromBytes

newtype CommitteeSize = CommitteeSize Integer
  deriving newtype (Eq, Show, Num, Integral, Real, Ord, Enum, NFData)

instance SignableRepresentation MembershipInput where
  getSignableRepresentation (MkMembershipInput x) = Hash.hashToBytes x

instance SignableRepresentation (VRF.CertifiedVRF VRF.PraosVRF v) where
  getSignableRepresentation = VRF.getOutputVRFBytes . VRF.certifiedOutput

castVote ::
  -- \| The thing we are voting on
  SignableRepresentation a =>
  a ->
  -- | Total stake of all voters
  Integer ->
  -- | The previous input to the VRF
  --  This is a basis for the VRF nonce, concatenated with the round number and the string @peras@
  --  to give the actual VRF input.
  MembershipInput ->
  -- | The target committee size, in the range [0, totalStake]
  CommitteeSize ->
  -- | The round number
  RoundNumber ->
  -- | The voter
  Voter ->
  -- | The vote, if the voter is selected
  Maybe (Vote a)
castVote blockHash totalStake (MkMembershipInput h) (CommitteeSize committeeSize) roundNumber@RoundNumber{unRoundNumber} MkVoter{..} =
  let nonce = mkNonce h unRoundNumber
      certVRF = VRF.evalCertified @_ @MembershipInput () nonce vrfSignKey
      certKES = KES.signKES () kesPeriod (getSignableRepresentation certVRF <> getSignableRepresentation blockHash) kesSignKey
      ratio = asInteger nonce % toInteger (maxBound @Word64)
   in case binomialVoteWeighing committeeSize ratio voterStake totalStake of
        0 -> Nothing
        n ->
          Just
            MkVote
              { creatorId = voterId
              , votingRound = roundNumber
              , blockHash
              , membershipProof = certVRF
              , votingWeight = n
              , sigKesPeriod = kesPeriod
              , signature = certKES
              }

asInteger :: MembershipInput -> Integer
asInteger (MkMembershipInput h) = fromIntegral $ fromBytesLE $ Hash.hashToBytes h
 where
  fromBytesLE = either error id . runGet getWord64le . BS.take 8

-- stolen from https://github.com/algorand/sortition/blob/main/sortition.cpp
binomialVoteWeighing ::
  -- | Expected committee size
  Integer ->
  -- | Outcome of "random" function, used to find voter's resulting weight
  -- Should be < 1
  Rational ->
  -- | Voter's stake
  Integer ->
  -- | Total stake
  Integer ->
  VotingWeight
binomialVoteWeighing expectedSize ratio voterStake totalStake =
  go 0 coin
 where
  n = voterStake
  p = expectedSize % totalStake
  ρ = fromRational ratio
  coin = fromIntegral voterStake
  cdf = binomial (fromIntegral n) (fromRational p)
  go a b =
    let c = (a + b) `div` 2
     in if abs (b - a) <= 1
          then VotingWeight b
          else case compare (cumulative cdf (fromIntegral c)) ρ of
            GT -> go a c
            LT -> go c b
            EQ -> VotingWeight c

type StakeDistribution = Map PartyId (VRF.VerKeyVRF VRF.PraosVRF, KES.VerKeyKES (KES.Sum6KES Ed25519DSIGN Blake2b_256), Integer)

checkVote :: SignableRepresentation a => StakeDistribution -> MembershipInput -> Vote a -> Bool
checkVote stakePools (MkMembershipInput h) MkVote{creatorId, votingRound = RoundNumber{unRoundNumber}, blockHash, membershipProof, votingWeight, sigKesPeriod, signature} =
  case Map.lookup creatorId stakePools of
    Nothing -> False
    Just (vrfKey, kesKey, _) ->
      VRF.verifyCertified () vrfKey nonce membershipProof
        && isRight
          ( KES.verifyKES
              ()
              kesKey
              sigKesPeriod
              (getSignableRepresentation membershipProof <> getSignableRepresentation blockHash)
              signature
          )
 where
  nonce = mkNonce h unRoundNumber
