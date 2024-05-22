{-# LANGUAGE DeriveGeneric #-}

module Peras.Abstract.Protocol.Types where

import Control.Concurrent.STM.TVar (TVar)
import Data.Map.Strict (Map)
import Data.Set (Set, singleton)
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import Peras.Block (Block, Certificate (MkCertificate), Party, Tx)
import Peras.Chain (Chain, Vote)
import Peras.Crypto (Hash (MkHash), LeadershipProof, MembershipProof)
import Peras.Numbering (RoundNumber, SlotNumber)
import Peras.Orphans ()

data PerasParams = PerasParams
  { perasU :: Integer
  -- ^ Round length.
  , perasA :: Integer
  -- ^ Certificate expiration age.
  , perasR :: Integer
  -- ^ Length of chain-ignorance period.
  , perasK :: Integer
  -- ^ Length of cool-down period.
  , perasL :: Integer
  -- ^ Minimum age for voted block.
  , perasτ :: Integer
  -- ^ Quorum size.
  , perasB :: Integer
  -- ^ Certificate boost.
  , perasΔ :: Integer
  -- ^ Delivery guarantee for diffusion.
  }
  deriving (Eq, Generic, Show)

-- FIXME: Should this included read-only items such as the `Party` and `PerasParams`?
data PerasState = PerasState
  { chainPref :: Chain
  , chains :: Set Chain
  , votes :: Set Vote
  , certs :: Map Certificate SlotNumber -- Note that VR-1A requires us to track when a certificate was received.
  , certPrime :: Certificate
  , certStar :: Certificate
  }
  deriving (Eq, Generic, Show)

initialState :: PerasState
initialState =
  PerasState
    { chainPref = genesisChain
    , chains = singleton genesisChain
    , votes = mempty
    , certs = mempty -- FIXME: Should this be `singleton genesisCert`?
    , certPrime = genesisCert
    , certStar = genesisCert
    }

type Fetching m = PerasParams -> Party -> TVar PerasState -> SlotNumber -> Set Chain -> Set Vote -> m (Either PerasError ())

type BlockCreation m = PerasParams -> Party -> TVar PerasState -> SlotNumber -> DiffuseBlock m -> m (Either PerasError ())

type Voting m = PerasParams -> Party -> TVar PerasState -> RoundNumber -> Preagreement m -> DiffuseVote m -> m (Either PerasError ())

type Preagreement m = PerasParams -> Party -> TVar PerasState -> RoundNumber -> m (Either PerasError (Maybe (Block, VotingWeight)))

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
  deriving (Eq, Generic, Ord, Show)

systemStart :: SlotNumber
systemStart = 0

genesisHash :: Hash Block
genesisHash = MkHash mempty

genesisChain :: Chain
genesisChain = mempty

genesisCert :: Certificate
genesisCert = MkCertificate 0 genesisHash
