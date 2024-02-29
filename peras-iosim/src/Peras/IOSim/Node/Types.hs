{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TemplateHaskell #-}

module Peras.IOSim.Node.Types (
  NodeState (NodeState),
  clock,
  committeeMember,
  downstreams,
  nodeId,
  rollbacks,
  owner,
  activeVotes,
  preferredChain,
  initialSeed,
  slot,
  slotLeader,
  stake,
  vrfOutput,
  blocksSeen,
) where

import Control.Lens (makeLenses)
import Control.Monad.Class.MonadTime (UTCTime)
import Data.Aeson (FromJSON, ToJSON)
import Data.Set (Set)
import GHC.Generics (Generic)
import Peras.Block (PartyId, Slot)
import Peras.Chain (Chain)
import Peras.IOSim.Types (Blocks, Coin, Rollback, Votes)
import Peras.Message (NodeId)
import Peras.Orphans ()

data NodeState = NodeState
  { _nodeId :: NodeId
  , _owner :: PartyId
  , _initialSeed :: Int
  , _clock :: UTCTime
  , _slot :: Slot
  , _stake :: Coin
  , _vrfOutput :: Double
  , _preferredChain :: Chain
  , _blocksSeen :: Blocks
  , _activeVotes :: Votes
  , _downstreams :: Set NodeId
  , _slotLeader :: Bool
  , _committeeMember :: Bool
  , _rollbacks :: [Rollback]
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON NodeState
instance ToJSON NodeState

makeLenses ''NodeState
