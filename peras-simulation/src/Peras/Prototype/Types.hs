{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.Prototype.Types (
  module Peras.Prototype.Types,
  module Peras.Conformance.Params,
) where

import Control.Concurrent.Class.MonadSTM (TVar)
import Data.Aeson (FromJSON, ToJSON)
import qualified Data.ByteString as BS
import Data.Default (Default (..))
import Data.Map.Strict (Map)
import Data.Set (Set, singleton)
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import Peras.Block (Block, Certificate (MkCertificate), Party, Tx)
import Peras.Chain (Chain, Vote)
import Peras.Conformance.Params
import Peras.Crypto (Hash (MkHash), LeadershipProof, MembershipProof, hash)
import Peras.Numbering (RoundNumber, SlotNumber)
import Peras.Orphans ()

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

instance FromJSON PerasState
instance ToJSON PerasState

instance Default PerasState where
  def = initialPerasState

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

type BlockCreation m = PerasParams -> Party -> TVar m PerasState -> SlotNumber -> [Tx] -> DiffuseChain m -> m (Either PerasError ())

type Voting m = PerasParams -> Party -> TVar m PerasState -> RoundNumber -> Preagreement m -> DiffuseVote m -> m (Either PerasError ())

type Preagreement m = PerasParams -> Party -> TVar m PerasState -> RoundNumber -> m (Either PerasError (Maybe (Block, VotingWeight)))

type DiffuseChain m = SlotNumber -> Chain -> m (PerasResult ())

type DiffuseVote m = SlotNumber -> Vote -> m (PerasResult ())

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
  | NoVoting
  | MultipleItemsDiffused
  deriving (Eq, Generic, Ord, Show)

systemStart :: SlotNumber
systemStart = 0

genesisHash :: Hash Block
genesisHash = MkHash (BS.replicate 8 0)

genesisChain :: Chain
genesisChain = mempty

hashTip :: Chain -> Hash Block
hashTip [] = genesisHash
hashTip (block : _) = hash block

genesisCert :: Certificate
genesisCert = MkCertificate 0 genesisHash

newRound :: Integral a => a -> PerasParams -> Bool
newRound s params = fromIntegral s `mod` perasU params == 0

inRound :: Integral a => a -> PerasParams -> RoundNumber
inRound s params = fromIntegral $ fromIntegral s `div` perasU params