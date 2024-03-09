{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}

module Peras.IOSim.Network.Types (
  Delay,
  Network (..),
  NetworkState,
  Reliability (..),
  Topology (..),
  activeNodes,
  blocksSeen,
  chainsSeen,
  currentStates,
  lastSlot,
  lastTime,
  networkRandom,
  pending,
  reliableLink,
  votesSeen,
) where

import Control.Concurrent.Class.MonadSTM.TQueue (TQueue)
import Control.Lens (makeLenses)
import Control.Monad.Class.MonadTime (UTCTime)
import Data.Default (Default (..))
import Data.Map.Strict (Map)
import Data.Set (Set)
import GHC.Generics (Generic)
import Peras.Block (Block, Slot)
import Peras.Chain (Chain, Vote)
import Peras.Crypto (Hash)
import Peras.IOSim.Experiment (Veto)
import Peras.IOSim.Hash (VoteHash)
import Peras.IOSim.Message.Types (InEnvelope, OutEnvelope)
import Peras.IOSim.Node.Types (NodeState)
import Peras.Message (NodeId)
import Peras.Orphans ()
import System.Random (StdGen, mkStdGen)

import Data.Aeson as A
import Generic.Random (genericArbitrary, uniform)
import Test.QuickCheck (Arbitrary (..))

type Delay = Int -- TODO: microseconds, not too fancy to avoid portability issues

newtype Reliability = Reliability Double
  deriving stock (Eq, Generic, Ord, Read, Show)
  deriving newtype (Num, Arbitrary, ToJSON, FromJSON)

data NodeLink = NodeLink
  { messageDelay :: Delay
  , reliability :: Reliability
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance ToJSON NodeLink
instance FromJSON NodeLink

reliableLink :: Delay -> NodeLink
reliableLink = (`NodeLink` 1)

instance Arbitrary NodeLink where
  arbitrary = genericArbitrary uniform

newtype Topology = Topology {connections :: Map NodeId (Map NodeId NodeLink)}
  deriving stock (Eq, Generic, Ord, Read, Show)
  deriving newtype (Arbitrary)

instance FromJSON Topology
instance ToJSON Topology

data Network m = Network
  { nodesIn :: Map NodeId (TQueue m InEnvelope)
  , nodesOut :: TQueue m OutEnvelope
  , veto :: Veto
  }
  deriving stock (Generic)

data NetworkState = NetworkState
  { _lastSlot :: Slot
  , _lastTime :: UTCTime
  , _activeNodes :: Set NodeId
  , _chainsSeen :: Map NodeId Chain
  -- ^ The latest "best" seen by nodes
  , _blocksSeen :: Map Hash (Set Block)
  , _votesSeen :: Map VoteHash Vote
  , _currentStates :: Map NodeId NodeState
  , _pending :: [OutEnvelope]
  , _networkRandom :: StdGen
  }
  deriving stock (Eq, Generic, Show)

instance Default NetworkState where
  def = NetworkState 0 (read "1970-01-01 00:00:00.0 UTC") mempty mempty mempty mempty mempty mempty $ mkStdGen 12345

-- FIXME: Is it okay to not serialize the random seed?
instance ToJSON NetworkState where
  toJSON NetworkState{..} =
    A.object
      [ "lastSlot" A..= _lastSlot
      , "lastTime" A..= _lastTime
      , "activeNodes" A..= _activeNodes
      , "chainsSeen" A..= _chainsSeen
      , "blocksSeen" A..= _blocksSeen
      , "votesSeen" A..= _votesSeen
      , "currentStates" A..= _currentStates
      , "pending" A..= _pending
      ]

makeLenses ''NetworkState
