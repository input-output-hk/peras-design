{-# LANGUAGE DeriveGeneric #-}

module Peras.Abstract.Protocol.Types where

import Control.Concurrent.Class.MonadSTM (TVar)
import Data.Map.Strict (Map)
import Data.Set (Set, singleton)
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import Peras.Block (Block, Certificate (MkCertificate), Party, Tx)
import Peras.Chain (Chain, Vote)
import Peras.Crypto (Hash (MkHash), LeadershipProof, MembershipProof)
import Peras.Numbering (RoundNumber, SlotNumber)
import Peras.Orphans ()

data PerasParams = MkPerasParams
  { perasU :: Integer
  -- ^ Round length, in slots
  , perasA :: Integer
  -- ^ Certificate expiration age, in slots
  , perasR :: Integer
  -- ^ Length of chain-ignorance period, in rounds
  , perasK :: Integer
  -- ^ Length of cool-down period, in slots
  , perasL :: Integer
  -- ^ Minimum age for voted block, in slots
  , perasτ :: Integer
  -- ^ Quorum size, as a percentage of total expected votes
  , perasB :: Integer
  -- ^ Certificate boost, in blocks
  , perasΔ :: Integer
  -- ^ Delivery guarantee for diffusion, in slots
  }
  deriving (Eq, Generic, Show)

-- FIXME: What are the actual values of T_heal, T_CQ, and T_CP?
-- For now I am assuming they all are in the order of security parameter, eg. 2160 on mainnet.
defaultParams :: PerasParams
defaultParams =
  MkPerasParams
    { perasU = 20
    , perasA = 2160
    , perasR = 100
    , perasK = 2160
    , perasL = 100
    , perasτ = 75
    , perasB = 100
    , perasΔ = 5
    }

-- FIXME: Should this included read-only items such as the `Party` and `PerasParams`?
data PerasState = MkPerasState
  { chainPref :: Chain
  , chains :: Set Chain
  , votes :: Set Vote
  , certs :: Map Certificate SlotNumber -- Note that VR-1A requires us to track when a certificate was received.
  , certPrime :: Certificate
  , certStar :: Certificate
  }
  deriving (Eq, Generic, Show)

initialPerasState :: PerasState
initialPerasState =
  MkPerasState
    { chainPref = genesisChain
    , chains = singleton genesisChain
    , votes = mempty
    , certs = mempty -- FIXME: Should this be `singleton genesisCert`?
    , certPrime = genesisCert
    , certStar = genesisCert
    }

type Fetching m = PerasParams -> Party -> TVar m PerasState -> SlotNumber -> Set Chain -> Set Vote -> m (Either PerasError ())

type BlockCreation m = PerasParams -> Party -> TVar m PerasState -> SlotNumber -> DiffuseBlock m -> m (Either PerasError ())

type Voting m = PerasParams -> Party -> TVar m PerasState -> RoundNumber -> Preagreement m -> DiffuseVote m -> m (Either PerasError ())

type Preagreement m = PerasParams -> Party -> TVar m PerasState -> RoundNumber -> m (Either PerasError (Maybe (Block, VotingWeight)))

type DiffuseBlock m = Block -> m (PerasResult ())

type DiffuseVote m = Vote -> m (PerasResult ())

type CreateSignedBlock m = Party -> SlotNumber -> Hash Block -> Maybe Certificate -> LeadershipProof -> Hash Payload -> m (PerasResult Block)

type CreateSignedCertificate m = Party -> Set Vote -> m (PerasResult Certificate)

type CreateSignedVote m = Party -> RoundNumber -> Hash Block -> MembershipProof -> VotingWeight -> m (PerasResult Vote)

type CreateLeadershipProof m = SlotNumber -> Set Party -> m (PerasResult LeadershipProof)

type CreateMembershipProof m = RoundNumber -> Set Party -> m (PerasResult MembershipProof)

type PerasResult a = Either PerasError a

type VotingWeight = Natural

type Payload = [Tx]

data PerasError
  = CertificateNotFound Certificate
  | BlockCreationFailed String
  | CertificationCreationFailed String
  | VoteCreationFailed String
  | NoVoting NoVotingReason
  deriving (Eq, Generic, Ord, Show)

data NoVotingReason
  = LastSeenCertNotFromPreviousRound Certificate RoundNumber
  | BlockDoesNotExtendLastSeenCert Block Certificate
  deriving (Eq, Generic, Ord, Show)

systemStart :: SlotNumber
systemStart = 0

genesisHash :: Hash Block
genesisHash = MkHash mempty

genesisChain :: Chain
genesisChain = mempty

genesisCert :: Certificate
genesisCert = MkCertificate 0 genesisHash
