{-# LANGUAGE DeriveGeneric #-}

module Peras.Abstract.Protocol.Types where

import Control.Concurrent.STM.TVar (TVar)
import Data.Set (Set, singleton)
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import Peras.Block (Block, Certificate (MkCertificate), Party, Tx)
import Peras.Chain (Chain, Vote)
import Peras.Crypto (Hash (MkHash), LeadershipProof)
import Peras.Numbering (RoundNumber, SlotNumber)
import Peras.Orphans ()

data PerasParams = PerasParams
  { perasU :: Natural
  -- ^ Round length.
  , perasA :: Natural
  -- ^ Certificate expiration age.
  , perasR :: Natural
  -- ^ Length of chain-ignorance period.
  , perasK :: Natural
  -- ^ Length of cool-down period.
  , perasΔ :: Natural
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

type Fetching m = TVar PerasState -> SlotNumber -> Set Chain -> Set Vote -> m ()

type BlockCreation m = TVar PerasState -> SlotNumber -> m ()

type Voting m = TVar PerasState -> RoundNumber -> Preagreement m -> m ()

type Preagreement m = TVar PerasState -> RoundNumber -> m (Maybe (Block, VotingWeight))

type CreateSignedBlock m = SlotNumber -> Party -> Hash Block -> Maybe Certificate -> LeadershipProof -> Payload -> m Block

type CreateSignedCertificate m = RoundNumber -> Set Vote -> m Certificate

type CreateSignedVote m = RoundNumber -> Party -> Hash Block -> LeadershipProof -> VotingWeight -> m Vote

type VotingWeight = Natural

type Payload = [Tx]

systemStart :: SlotNumber
systemStart = 0

genesisHash :: Hash Block
genesisHash = MkHash mempty

genesisChain :: Chain
genesisChain = mempty

genesisCert :: Certificate
genesisCert = MkCertificate 0 genesisHash
