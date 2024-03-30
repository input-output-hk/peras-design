{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns #-}

module Peras.IOSim.Chain (
  BlockTree,
  ChainIndex (..),
  ChainState (..),
  ChainTracker (..),
  preferredVotes,
  preferredCerts,
) where

import Data.Aeson (FromJSON, ToJSON)
import Data.Default (Default (def))
import GHC.Generics (Generic)
import Peras.Block (Block, BlockBody, Certificate)
import Peras.Chain (Chain, RoundNumber, Vote)
import Peras.IOSim.Hash (BlockHash, BodyHash, CertificateHash, VoteHash)
import Peras.Message (NodeId)
import Peras.Orphans ()
import Test.QuickCheck (Arbitrary (..))

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Tree as T

type BlockTree = T.Forest Block

data ChainIndex = ChainIndex
  { headerIndex :: M.Map BlockHash Block
  , bodyIndex :: M.Map BodyHash BlockBody
  , voteIndex :: M.Map VoteHash Vote
  , certIndex :: M.Map CertificateHash Certificate
  , votesByRound :: M.Map RoundNumber (S.Set VoteHash)
  , certsByRound :: M.Map RoundNumber (S.Set VoteHash)
  , weightIndex :: M.Map BlockHash Double
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON ChainIndex
instance ToJSON ChainIndex

instance Default ChainIndex where
  def = ChainIndex def def def def def def def

instance Arbitrary ChainIndex where
  arbitrary = pure def

data ChainTracker = ChainTracker
  { preferredChain :: Chain
  , preferredVoteHashes :: S.Set VoteHash
  , preferredCertHashes :: S.Set CertificateHash
  , missingBodies :: S.Set BodyHash
  , latestSeen :: Maybe Certificate
  , latestPreferred :: Maybe Certificate
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON ChainTracker
instance ToJSON ChainTracker

instance Default ChainTracker where
  def = ChainTracker def def def def def def

instance Arbitrary ChainTracker where
  arbitrary = pure def

data ChainState = ChainState
  { tracker :: ChainTracker
  , channelTrackers :: M.Map NodeId ChainTracker
  , chainIndex :: ChainIndex
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON ChainState
instance ToJSON ChainState

instance Default ChainState where
  def = ChainState def def def

instance Arbitrary ChainState where
  arbitrary = pure def

preferredVotes :: ChainIndex -> ChainTracker -> [Vote]
preferredVotes ChainIndex{voteIndex} ChainTracker{preferredVoteHashes} =
  M.elems $ M.restrictKeys voteIndex preferredVoteHashes

preferredCerts :: ChainIndex -> ChainTracker -> [Certificate]
preferredCerts ChainIndex{certIndex} ChainTracker{preferredCertHashes} =
  M.elems $ M.restrictKeys certIndex preferredCertHashes
