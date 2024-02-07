{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

module Peras.IOSim.Node.Types (
  NodeProcess(..)
, NodeState(..)
) where

import Control.Concurrent.Class.MonadSTM.TQueue (TQueue)
import Control.Monad.Class.MonadTime (UTCTime)
import GHC.Generics (Generic)
import Peras.IOSim.Types (Chain, NodeId, SlotNo)
import Peras.IOSim.Message.Types (InEnvelope, OutEnvelope)

import qualified Data.Set as S

data NodeState =
  NodeState
  {
    nodeId :: NodeId
  , clock :: UTCTime
  , slotNo :: SlotNo
  , vrfOutput :: Double
  , preferredChain :: Chain
  , downstreams :: S.Set NodeId
  }
    deriving stock (Eq, Generic, Ord, Read, Show)

data NodeProcess m =
  NodeProcess
  {
    incoming :: TQueue m InEnvelope
  , outgoing :: TQueue m OutEnvelope
  }
    deriving stock (Generic)
