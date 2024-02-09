{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}

module Peras.IOSim.Network.Types (
  Network(..)
, NetworkState
, Topology(..)
, activeNodes
, lastSlot
, lastTime
) where

import Control.Concurrent.Class.MonadSTM.TQueue (TQueue)
import Control.Lens (makeLenses)
import Control.Monad.Class.MonadTime (UTCTime)
import Data.Default (Default(..))
import GHC.Generics (Generic)
import Peras.Block (Slot)
import Peras.IOSim.Message.Types (OutEnvelope, InEnvelope)
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

data Network t m =
  Network
  {
    nodesIn :: M.Map NodeId (TQueue m (InEnvelope t))
  , nodesOut :: TQueue m (OutEnvelope t)
  }
  deriving stock (Generic)

data NetworkState =
  NetworkState
  {
    _lastSlot :: Slot
  , _lastTime :: UTCTime
  , _activeNodes :: S.Set NodeId
  }
    deriving stock (Eq, Generic, Ord, Read, Show)

instance Default NetworkState where
  def = NetworkState 0 (read "2000-01-01 00:00:00.0 UTC") mempty

instance ToJSON NetworkState where
  toJSON NetworkState{..} =
    A.object
      [
        "lastSlot" A..= _lastSlot
      , "lastTime" A..= _lastTime
      , "activeNodes" A..= _activeNodes
      ]

makeLenses ''NetworkState
