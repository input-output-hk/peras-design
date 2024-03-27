{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module Peras.IOSim.Network.Types (
  Delay,
  Network (..),
  NetworkState,
  NodeLink (..),
  Reliability (..),
  Topology (..),
  blocksSeen,
  chainsSeen,
  currentStates,
  lastSlot,
  lastTime,
  networkRandom,
  networkStake,
  networkDelay,
  networkVeto,
  pending,
  reliableLink,
  votesSeen,
) where

import Control.Concurrent.Class.MonadSTM.TQueue (TQueue)
import Control.Lens (makeLenses)
import Control.Monad.Class.MonadTime (UTCTime)
import Data.Default (Default (..))
import Data.Map.Strict (Map)
import GHC.Generics (Generic)
import Generic.Random (genericArbitrary, uniform)
import Peras.Block (Block (parentBlock), Slot)
import Peras.Chain (Chain, Vote)
import Peras.Event (CpuTime)
import Peras.IOSim.Experiment (Veto, noVeto)
import Peras.IOSim.Hash (BlockHash, VoteHash)
import Peras.IOSim.Message.Types (InEnvelope, OutEnvelope)
import Peras.IOSim.Node.Types (PerasNode (getBlocks, getPreferredChain, getVotes))
import Peras.IOSim.Nodes (SomeNode)
import Peras.IOSim.Types (Coin, simulationStart)
import Peras.Message (NodeId)
import Peras.Orphans ()
import System.Random (StdGen, mkStdGen)
import Test.QuickCheck (Arbitrary (..))

import Data.Aeson as A
import qualified Data.Map as M
import qualified Data.PQueue.Min as PQ
import qualified Data.Set as S

type Delay = Int -- TODO: microseconds, not too fancy to avoid portability issues

newtype Reliability = Reliability Double
  deriving stock (Eq, Generic, Ord, Read, Show)
  deriving newtype (Num, Arbitrary, ToJSON, FromJSON)

data NodeLink = NodeLink
  { latency :: Delay
  , reliability :: Reliability
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance ToJSON NodeLink
instance FromJSON NodeLink

reliableLink :: Delay -> NodeLink
reliableLink = flip NodeLink 1

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
  , _currentStates :: Map NodeId SomeNode
  , _pending :: PQ.MinQueue OutEnvelope
  , _networkStake :: Coin
  , _networkVeto :: Veto
  , _networkDelay :: NodeId -> NodeId -> Maybe CpuTime
  , _networkRandom :: StdGen
  }

instance Show NetworkState where
  show NetworkState{..} =
    "NetworkState {lastSlot = "
      <> show _lastSlot
      <> ", lastTime ="
      <> show _lastTime
      <> ", currentStates ="
      <> show _currentStates
      <> ", pending = "
      <> show _pending
      <> ", networkStake = "
      <> show _networkStake
      <> ", networkRandom = "
      <> show _networkRandom
      <> "}"

instance Default NetworkState where
  def = NetworkState 0 simulationStart mempty mempty def noVeto (const $ const def) $ mkStdGen 12345

{-# DEPRECATED chainsSeen "Use observability instead." #-}
chainsSeen :: NetworkState -> M.Map NodeId Chain
chainsSeen = M.map getPreferredChain . _currentStates

{-# DEPRECATED blocksSeen "Use observability instead." #-}
blocksSeen :: NetworkState -> M.Map BlockHash (S.Set Block)
blocksSeen state =
  let
    index = M.unions $ getBlocks <$> M.elems (_currentStates state)
   in
    M.foldr (\block -> M.insertWith S.union (parentBlock block) $ S.singleton block) def index

{-# DEPRECATED votesSeen "Use observability instead." #-}
votesSeen :: NetworkState -> M.Map VoteHash Vote
votesSeen = M.unions . fmap getVotes . M.elems . _currentStates

-- FIXME: Is it okay to not serialize the random seed?
instance ToJSON NetworkState where
  toJSON state@NetworkState{..} =
    A.object
      [ "lastSlot" A..= _lastSlot
      , "lastTime" A..= _lastTime
      , "chainsSeen" A..= chainsSeen state
      , "currentStates" A..= _currentStates
      , "pending" A..= PQ.toList _pending
      ]

makeLenses ''NetworkState
{-# DEPRECATED lastSlot "Use observability instead." #-}
{-# DEPRECATED lastTime "Use observability instead." #-}
