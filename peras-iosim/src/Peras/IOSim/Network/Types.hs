{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

module Peras.IOSim.Network.Types (
  Network(..)
, Topology(..)
) where

import Control.Concurrent.Class.MonadSTM.TQueue (TQueue)
import GHC.Generics (Generic)
import Peras.IOSim.Message.Types (OutEnvelope, InEnvelope)
import Peras.IOSim.Types (NodeId)

import Data.Map.Strict as M
import Data.Set as S

newtype Topology = Topology {connections :: M.Map NodeId (S.Set NodeId)}
  deriving stock (Eq, Generic, Ord, Read, Show)

data Network m =
  Network
  {
    nodesIn :: M.Map NodeId (TQueue m InEnvelope)
  , nodesOut :: TQueue m OutEnvelope
  }
  deriving stock (Generic)
