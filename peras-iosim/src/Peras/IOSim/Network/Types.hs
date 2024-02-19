{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}

module Peras.IOSim.Network.Types (
  Network (..),
  NetworkState,
  Topology (..),
  activeNodes,
  chainsSeen,
  networkRandom,
  currentStates,
  lastSlot,
  lastTime,
  pending,
) where

import Control.Concurrent.Class.MonadSTM.TQueue (TQueue)
import Control.Lens (makeLenses)
import Control.Monad.Class.MonadTime (UTCTime)
import Data.Default (Default (..))
import GHC.Generics (Generic)
import Peras.Block (Slot)
import Peras.Chain (Chain)
import Peras.IOSim.Message.Types (InEnvelope, OutEnvelope)
import Peras.IOSim.Node.Types (NodeState)
import Peras.IOSim.Types (Votes)
import Peras.Message (NodeId)
import Peras.Orphans ()
import System.Random (StdGen, mkStdGen)

import Data.Aeson as A
import Data.Map.Strict as M
import Data.Set as S

newtype Topology = Topology {connections :: M.Map NodeId (S.Set NodeId)}
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON Topology where
  parseJSON = A.withObject "Topology" $ \o -> Topology <$> o A..: "connections"

instance ToJSON Topology where
  toJSON Topology{..} = A.object ["connections" A..= connections]

data Network m = Network
  { nodesIn :: M.Map NodeId (TQueue m InEnvelope)
  , nodesOut :: TQueue m OutEnvelope
  }
  deriving stock (Generic)

data NetworkState = NetworkState
  { _lastSlot :: Slot
  , _lastTime :: UTCTime
  , _activeNodes :: S.Set NodeId
  , _chainsSeen :: S.Set (Chain Votes)
  , _currentStates :: M.Map NodeId NodeState
  , _pending :: [OutEnvelope]
  , _networkRandom :: StdGen -- FIXME: Is it okay not to serialize this?
  }
  deriving stock (Eq, Generic, Show)

instance Default NetworkState where
  def = NetworkState 0 (read "1970-01-01 00:00:00.0 UTC") mempty mempty M.empty mempty $ mkStdGen 12345

instance ToJSON NetworkState where
  toJSON NetworkState{..} =
    A.object
      [ "lastSlot" A..= _lastSlot
      , "lastTime" A..= _lastTime
      , "activeNodes" A..= _activeNodes
      , "chainsSeen" A..= _chainsSeen
      , "currentStates" A..= _currentStates
      , "pending" A..= _pending
      ]

makeLenses ''NetworkState
