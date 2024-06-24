{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Peras.Voting.Vote where

import Cardano.Binary (FromCBOR (..), ToCBOR (..))
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
import Data.Serialize (getWord64be, putWord64le, runGet, runPut)
import Data.Word (Word64)
import GHC.Generics (Generic)
import Numeric.SpecFunctions (incompleteBeta)

data Vote block = MkVote
  { creatorId :: PartyId
  , votingRound :: RoundNumber
  , blockHash :: block
  , membershipProof :: MembershipProof
  , votingWeight :: VotingWeight
  , sigKesPeriod :: KES.Period
  , signature :: Signature
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (NFData)

instance ToCBOR block => ToCBOR (Vote block) where
  toCBOR MkVote{creatorId, votingRound, blockHash, membershipProof, votingWeight, sigKesPeriod, signature} =
    toCBOR creatorId
      <> toCBOR votingRound
      <> toCBOR blockHash
      <> toCBOR membershipProof
      <> toCBOR votingWeight
      <> toCBOR sigKesPeriod
      <> toCBOR signature

instance FromCBOR block => FromCBOR (Vote block) where
  fromCBOR =
    MkVote
      <$> fromCBOR
      <*> fromCBOR
      <*> fromCBOR
      <*> fromCBOR
      <*> fromCBOR
      <*> fromCBOR
      <*> fromCBOR

newtype VotingWeight = VotingWeight {unVotingWeight :: Word64}
  deriving stock (Eq, Ord, Show)
  deriving newtype (Num, Integral, Real, Enum, NFData, ToCBOR, FromCBOR)

-- | A party (SPO) is identified by its pool ID which is the hash of its VRF verification key.
newtype PartyId = MkPartyId {unPartyId :: Hash Blake2b_256 (VRF.VerKeyVRF VRF.PraosVRF)}
  deriving stock (Eq, Ord, Show)
  deriving newtype (NFData, ToCBOR, FromCBOR)

mkPartyId :: BS.ByteString -> PartyId
mkPartyId = MkPartyId . fromJust . Hash.hashFromBytes

-- | A round number is just a natural number.
newtype RoundNumber = RoundNumber {unRoundNumber :: Word64}
  deriving newtype (Eq, Ord, Show, Num, Integral, Real, Enum, NFData, ToCBOR, FromCBOR)

type MembershipProof = VRF.CertifiedVRF VRF.PraosVRF MembershipInput

deriving anyclass instance NFData (VRF.CertifiedVRF VRF.PraosVRF MembershipInput)

type Signature = KES.SigKES (KES.Sum6KES Ed25519DSIGN Blake2b_256)

-- | The input to the `evalVRF` is a hash value.
newtype MembershipInput = MkMembershipInput {unNonce :: Hash Blake2b_256 MembershipInput}
  deriving newtype (Eq, Ord, Show, NFData)

fromBytes :: BS.ByteString -> MembershipInput
fromBytes = MkMembershipInput . fromJust . Hash.hashFromBytes

mkNonce :: Hash Blake2b_256 a -> Word64 -> MembershipInput
mkNonce h unRoundNumber =
  MkMembershipInput
    . Hash.castHash
    . Hash.hashWith id
    $ Hash.hashToBytes h <> "peras" <> LBS.toStrict (BS.toLazyByteString (BS.word64BE unRoundNumber))

-- | A voter (eg. stake pool operator) and its associated keys.
--
-- Of course, in practice the signing keys would only be knonw to the
-- actual party and the verifiers only have access to verification
-- keys from the stake pool registration certificate and stake
-- distribution.
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

-- | Cast a vote for a given block and nonce.
--
-- This function uses the VRF to determine if the voter is selected to
-- vote, based on a target `committeeSize`, `voterStake`and
-- `totalStake` of all voters. It returns either `Nothing` if the
-- voter has not enough weight, or a `Vote` with a `VotingWeight`
-- corresponding to the voter's relative share. The `VotingWeight` is
-- computed using `binomialVoteWeighing` function with the output of
-- the VRF function as the random value.
castVote ::
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
  let certVRF = VRF.evalCertified @_ @MembershipInput () nonce vrfSignKey
      certKES = KES.signKES () kesPeriod (getSignableRepresentation certVRF <> getSignableRepresentation blockHash) kesSignKey
      nonce@(MkMembershipInput h') = mkNonce h unRoundNumber
      ratio = asInteger h' % toInteger (maxBound @Word64)
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

-- | Convert a hash to a 64-bit unsigned integer.
--
-- This function assumes the given hash represents a big-endian natural value and
-- truncates it to 64 bits, converting it to an unsigned integer assuming big endian
-- ordering.
--
-- NOTE: This function is faster and much simpler than the
-- [one](https://github.com/input-output-hk/cardano-base/blob/a9bfdf50b7794c962f73f06763546dc65257720e/cardano-crypto-class/src/Cardano/Crypto/Util.hs#L139)
-- used in the actual ledger code base, which should be
-- preferred. While the distribution it produces is good enough for
-- our purposes, it is much easier to attack as an adversary only has
-- to try to tweak 64 bits of the hash instead of 256.  We assume the
-- performance profile of this simple, naive function is similar to
-- the highly optimised production one.
asInteger :: Hash Blake2b_256 a -> Integer
asInteger h = fromIntegral $ fromBytesLE $ Hash.hashToBytes h
 where
  fromBytesLE = either error id . runGet getWord64be . BS.take 8 . BS.drop 24

-- | Compute a vote's weight based on binomial distribution of the
-- possible weights.
--
-- This function is directly stolen from
-- [Algorand's](https://github.com/algorand/sortition/blob/main/sortition.cpp)
-- sortition codebase. It computes the actual voting weight through a
-- dichotomial search in the binomial distribution $B(n,p)$ where $n$
-- is the voter's stake (in ADA) and $p$ is the ratio of target
-- committee size over the total stake.  The value searched for is the
-- given `ratio` which is compared to quantiles of the distribution.
--
-- NOTE: While this is significantly faster, by several orders of
-- magnitude, to the lottery drawing (see `isLotteryWinner`) process,
-- the soundness of this process has not been researched so it should
-- be considered with some caution.
binomialVoteWeighing ::
  -- | Expected committee size
  Integer ->
  -- | Outcome of "random" function, used to find voter's resulting weight
  -- must be < 1
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
  distribution = Binomial n (fromRational p)
  go a b =
    let c = (a + b) `div` 2
     in if abs (b - a) <= 1
          then VotingWeight b
          else case compare (cumulative distribution (fromIntegral c)) ρ of
            GT -> go a c
            LT -> go c b
            EQ -> VotingWeight c

-- | Binomial distribution
data Binomial = Binomial {n :: Integer, p :: Double}

-- | CDF of the binomial distribution using the incomplete beta
-- function.  This code is directly stolen from the
-- [statistics](https://hackage.haskell.org/package/statistics-0.16.2.1/docs/src/Statistics.Distribution.Binomial.html#cumulative)
-- package but uses an `Integer` instead of an `Int` for the binomial
-- distribution's number of trials.
cumulative :: Binomial -> Double -> Double
cumulative (Binomial n p) x
  | isNaN x = error "Statistics.Distribution.Binomial.cumulative: NaN input"
  | isInfinite x = if x > 0 then 1 else 0
  | k < 0 = 0
  | k >= n = 1
  | otherwise = incompleteBeta (fromIntegral (n - k)) (fromIntegral (k + 1)) (1 - p)
 where
  k = floor x

data VotingParameters = VotingParameters
  { k :: Integer
  -- ^ The number of voters in the committee
  , m :: Integer
  , f :: Rational
  }

-- | Standard parameters for mainnet committee selection.
--
-- These parameters are the ones used for Mithril mainnet certificate production,
-- see https://mithril.network for more details.
standardParameters :: VotingParameters
standardParameters =
  VotingParameters
    { k = 2422
    , m = 20_973
    , f = 0.2
    }

castVote' ::
  SignableRepresentation a =>
  -- | The thing to vote on
  a ->
  -- | Total stake of all voters
  Integer ->
  -- | The previous input to the VRF
  --  This is a basis for the VRF nonce, concatenated with the round number and the string @peras@
  --  to give the actual VRF input.
  MembershipInput ->
  -- | The voting parameters
  VotingParameters ->
  -- | The round number
  RoundNumber ->
  -- | The voter
  Voter ->
  -- | The vote, if the voter is selected
  Maybe (Vote a)
castVote' blockHash totalStake (MkMembershipInput h) VotingParameters{k, m, f} roundNumber@RoundNumber{unRoundNumber} MkVoter{..} =
  let certVRF = VRF.evalCertified @_ @MembershipInput () nonce vrfSignKey
      certKES = KES.signKES () kesPeriod (getSignableRepresentation certVRF <> getSignableRepresentation blockHash) kesSignKey
      nonce@(MkMembershipInput h') = mkNonce h unRoundNumber
      c = log $ fromRational (1 - f)
      certNatMax = toInteger $ maxBound @Word64
      checkVoteAtIndex i =
        let h'' = Hash.hashWith @Blake2b_256 id $ Hash.hashToBytes h' <> runPut (putWord64le $ fromIntegral i)
         in isLotteryWinner (asInteger h'') certNatMax (voterStake % totalStake) c
      votingWeight = length $ filter checkVoteAtIndex [0 .. m - 1]
   in case votingWeight of
        0 -> Nothing
        n ->
          Just
            MkVote
              { creatorId = voterId
              , votingRound = roundNumber
              , blockHash
              , membershipProof = certVRF
              , votingWeight = fromIntegral n
              , sigKesPeriod = kesPeriod
              , signature = certKES
              }

-- | Taylor expansion-based single voting
-- stolen from https://github.com/input-output-hk/cardano-ledger/blob/e2aaf98b5ff2f0983059dc6ea9b1378c2112101a/libs/cardano-protocol-tpraos/src/Cardano/Protocol/TPraos/BHeader.hs#L434
isLotteryWinner ::
  -- | Value to check probability against
  Integer ->
  -- | Upper bound of the value
  Integer ->
  -- | The stake of the voter
  Rational ->
  -- | The `ln (1 - f)`  coefficient
  Double ->
  Bool
isLotteryWinner certNat certNatMax σ c =
  case taylorExpCmp 3 recip_q x of
    BELOW -> True
    ABOVE -> False
    MaxReached -> False
 where
  recip_q = fromRational $ certNatMax % (certNatMax - certNat)
  x = -fromRational σ * c

data CompareResult
  = BELOW
  | ABOVE
  | MaxReached
  deriving (Show, Eq)

-- | Efficient way to compare the result of the Taylor expansion of the
-- exponential function to a threshold value.
-- Stolen from https://github.com/input-output-hk/cardano-ledger/blob/e2aaf98b5ff2f0983059dc6ea9b1378c2112101a/libs/non-integral/src/Cardano/Ledger/NonIntegral.hs#L197
taylorExpCmp :: forall a. RealFrac a => a -> a -> a -> CompareResult
taylorExpCmp boundX cmp x = go 1000 0 x 1 1
 where
  go :: Int -> Int -> a -> a -> a -> CompareResult
  go maxN n err acc divisor
    | maxN == n = MaxReached
    | cmp >= acc' + errorTerm = ABOVE
    | cmp < acc' - errorTerm = BELOW
    | otherwise = go maxN (n + 1) err' acc' divisor'
   where
    errorTerm = abs (err' * boundX)
    divisor' = divisor + 1
    nextX = err
    err' = (err * x) / divisor'
    acc' = acc + nextX

type StakeDistribution = Map PartyId (VRF.VerKeyVRF VRF.PraosVRF, KES.VerKeyKES (KES.Sum6KES Ed25519DSIGN Blake2b_256), Integer)

mkStakeDistribution :: [Voter] -> StakeDistribution
mkStakeDistribution voters =
  Map.fromList $
    [ (voterId, (vrfVerKey, kesVerKey, voterStake))
    | MkVoter{voterId, vrfVerKey, kesVerKey, voterStake} <- voters
    ]

checkVote :: SignableRepresentation a => CommitteeSize -> Integer -> StakeDistribution -> MembershipInput -> Vote a -> Bool
checkVote committeeSize totalStake stakePools (MkMembershipInput h) vote =
  case Map.lookup creatorId stakePools of
    Nothing -> False
    Just (vrfKey, kesKey, voterStake) ->
      checkVRF vrfKey
        && checkSignature kesKey
        && checkWeight voterStake
 where
  checkWeight voterStake =
    case binomialVoteWeighing (fromIntegral committeeSize) ratio voterStake totalStake of
      0 -> False
      n -> n == votingWeight

  checkVRF vrfKey = VRF.verifyCertified () vrfKey nonce membershipProof

  checkSignature kesKey =
    isRight
      ( KES.verifyKES
          ()
          kesKey
          sigKesPeriod
          (getSignableRepresentation membershipProof <> getSignableRepresentation blockHash)
          signature
      )
  MkVote{creatorId, votingRound = RoundNumber{unRoundNumber}, blockHash, membershipProof, votingWeight, sigKesPeriod, signature} = vote
  nonce@(MkMembershipInput h') = mkNonce h unRoundNumber
  ratio = asInteger h' % toInteger (maxBound @Word64)
