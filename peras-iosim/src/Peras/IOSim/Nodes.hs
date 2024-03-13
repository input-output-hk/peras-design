{-# LANGUAGE DeriveGeneric #-}

module Peras.IOSim.Nodes (
  SomeNode (..),
) where

import Data.Aeson (FromJSON, ToJSON)
import Data.Bifunctor (second)
import GHC.Generics (Generic)
import Peras.IOSim.Node.Types (PerasNode (..))

import qualified Peras.IOSim.Nodes.Honest as Honest (Node)

-- FIXME: Ideally, this would be an existential type, but that makes deriving instances problematic and it could also impact interoperability with Rust.
newtype SomeNode = HonestNode Honest.Node
  deriving (Eq, Generic, Ord, Read, Show)

instance FromJSON SomeNode
instance ToJSON SomeNode

instance PerasNode SomeNode where
  getNodeId (HonestNode n) = getNodeId n
  getOwner (HonestNode n) = getOwner n
  getStake (HonestNode n) = getStake n
  setStake (HonestNode n) = HonestNode . setStake n
  getDownstreams (HonestNode n) = getDownstreams n
  getPreferredChain (HonestNode n) = getPreferredChain n
  getBlocks (HonestNode n) = getBlocks n
  getVotes (HonestNode n) = getVotes n
  handleMessage (HonestNode n) = (fmap (second HonestNode) .) . handleMessage n
  stop (HonestNode n) = fmap HonestNode . stop n
