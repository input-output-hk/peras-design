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
  exitStates,
  lastSlot,
  lastTime,
) where

import Control.Concurrent.Class.MonadSTM.TQueue (TQueue)
import Control.Lens (makeLenses)
import Control.Monad.Class.MonadTime (UTCTime)
import Data.Default (Default (..))
import GHC.Generics (Generic)
import Peras.Block (Slot)
import Peras.IOSim.Message.Types (InEnvelope, OutEnvelope)
import Peras.IOSim.Node.Types (NodeState)
import Peras.Message (NodeId)
import Peras.Orphans ()

import Data.Aeson as A
import Data.Map.Strict as M
import Data.Set as S

newtype Topology = Topology {connections :: M.Map NodeId (S.Set NodeId)}
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON Topology where
  parseJSON = A.withObject "Topology" $ \o -> Topology <$> o A..: "connections"

instance ToJSON Topology where
  toJSON Topology{..} = A.object ["connections" A..= connections]

data Network v m = Network
  { nodesIn :: M.Map NodeId (TQueue m (InEnvelope v))
  , nodesOut :: TQueue m (OutEnvelope v)
  }
  deriving stock (Generic)

data NetworkState v = NetworkState
  { _lastSlot :: Slot
  , _lastTime :: UTCTime
  , _activeNodes :: S.Set NodeId
  , _exitStates :: M.Map NodeId (NodeState v)
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance Default (NetworkState v) where
  def = NetworkState 0 (read "1970-01-01 00:00:00.0 UTC") mempty M.empty

instance ToJSON v => ToJSON (NetworkState v) where
  toJSON NetworkState{..} =
    A.object
      [ "lastSlot" A..= _lastSlot
      , "lastTime" A..= _lastTime
      , "activeNodes" A..= _activeNodes
      , "exitStates" A..= _exitStates
      ]

makeLenses ''NetworkState
