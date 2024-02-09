{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Network.Types (
  Network(..)
, Topology(..)
) where

import Control.Concurrent.Class.MonadSTM.TQueue (TQueue)
import GHC.Generics (Generic)
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
