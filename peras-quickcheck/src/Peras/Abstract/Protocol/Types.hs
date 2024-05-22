{-# LANGUAGE DeriveGeneric #-}

module Peras.Abstract.Protocol.Types where

import Control.Concurrent.STM.TVar (TVar)
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
  , perasΔ :: Integer
  -- ^ Delivery guarantee for diffusion.
  }
  deriving (Eq, Generic, Show)

data PerasState = PerasState
  { chainPref :: Chain
  , chains :: Set Chain
  , votes :: Set Vote
  , certs :: Set Certificate
  , certPrime :: (Certificate, SlotNumber)
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
    , certPrime = (genesisCert, systemStart)
    , certStar = genesisCert
    }

type Fetching m = PerasParams -> TVar PerasState -> SlotNumber -> Set Chain -> Set Vote -> m ()

type BlockCreation m = PerasParams -> TVar PerasState -> SlotNumber -> DiffuseBlock m -> m ()

type Voting m = PerasParams -> TVar PerasState -> RoundNumber -> Preagreement m -> DiffuseVote m -> m ()

type Preagreement m = PerasParams -> TVar PerasState -> RoundNumber -> m (Maybe (Block, VotingWeight))

type DiffuseBlock m = Block -> m ()

type DiffuseVote m = Vote -> m ()

type CreateSignedBlock m = Party -> SlotNumber -> Hash Block -> Maybe Certificate -> LeadershipProof -> Hash Payload -> m (Either CryptoError Block)

type CreateSignedCertificate m = Party -> RoundNumber -> Set Vote -> m (Either CryptoError Certificate)

type CreateSignedVote m = Party -> RoundNumber -> Hash Block -> MembershipProof -> VotingWeight -> m (Either CryptoError Vote)

type CreateLeadershipProof m = SlotNumber -> Set Party -> m (Either CryptoError LeadershipProof)

type CreateMembershipProof m = RoundNumber -> Set Party -> m (Either CryptoError MembershipProof)

type VotingWeight = Natural

type Payload = [Tx]

data CryptoError
  = BlockCreationFailed String
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
