{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

module Peras.IOSim.Chain.Types (
  ChainState (..),
  BlockTree (..),
) where

import Data.Aeson (FromJSON, ToJSON)
import Data.Default (Default (def))
import GHC.Generics (Generic)
import Peras.Block (Block (..))
import Peras.Chain (Chain (..), RoundNumber)
import Peras.IOSim.Hash (BlockHash, VoteHash)
import Peras.IOSim.Types (Vote')
import Peras.Orphans ()
import Test.QuickCheck (Arbitrary (..))

import qualified Data.Map as M
import qualified Data.Set as S

data BlockTree
  = Genesis
  | BlockTree
      { parentBlock :: Block
      , childBlocks :: BlockTree
      }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON BlockTree
instance ToJSON BlockTree

instance Default BlockTree where
  def = Genesis

data ChainState = ChainState
  { preferredChain :: Chain
  , blockIndex :: M.Map BlockHash Block
  , voteIndex :: M.Map VoteHash Vote'
  , blockTree :: BlockTree
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