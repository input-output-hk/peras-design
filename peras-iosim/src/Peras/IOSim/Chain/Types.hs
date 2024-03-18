{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

module Peras.IOSim.Chain.Types (
  BlockTree,
  ChainState (..),
) where

import Data.Aeson (FromJSON, ToJSON)
import Data.Default (Default (def))
import GHC.Generics (Generic)
import Peras.Block (Block, BlockBody)
import Peras.Chain (Chain, RoundNumber, Vote)
import Peras.IOSim.Hash (BlockHash, BodyHash, VoteHash)
import Peras.Orphans ()
import Test.QuickCheck (Arbitrary (..))

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Tree as T

type BlockTree = T.Forest Block

data ChainState = ChainState
  { preferredChain :: Chain
  , blockIndex :: M.Map BlockHash Block
  , bodyIndex :: M.Map BodyHash BlockBody
  , voteIndex :: M.Map VoteHash Vote
  , danglingBlocks :: S.Set BlockHash
  , danglingVotes :: S.Set VoteHash
  , votesByRound :: M.Map RoundNumber (M.Map BlockHash (S.Set VoteHash))
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON ChainState
instance ToJSON ChainState

instance Default ChainState where
  def = ChainState def def def def def def def

instance Arbitrary ChainState where
  arbitrary = pure def
