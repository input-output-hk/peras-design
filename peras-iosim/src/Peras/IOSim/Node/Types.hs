{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Node.Types (
  NodeProcess(..)
, NodeState(..)
) where

import Control.Concurrent.Class.MonadSTM.TQueue (TQueue)
import Control.Monad.Class.MonadTime (UTCTime)
import GHC.Generics (Generic)
import Peras.Block (Slot)
import Peras.Chain (Chain)
import Peras.IOSim.Message.Types (InEnvelope, OutEnvelope)
import Peras.IOSim.Protocol.Types (Protocol)
import Peras.IOSim.Types (Currency)
import Peras.Message(NodeId)

import qualified Data.Aeson as A
import qualified Data.Set as S

data NodeState t =
  NodeState
  {
    nodeId :: NodeId
  , protocol :: Protocol
  , clock :: UTCTime
  , slot :: Slot
  , stake :: Currency
  , vrfOutput :: Double
  , preferredChain :: Chain t
  , downstreams :: S.Set NodeId
  }
    deriving stock (Eq, Generic, Ord, Read, Show)

instance A.FromJSON t => A.FromJSON (NodeState t) where
  parseJSON =
    A.withObject "NodeState"
      $ \o ->
        do
          nodeId <- o A..: "nodeId"
          protocol <- o A..: "protocol"
          clock <- o A..: "clock"
          slot <- o A..: "slot"
          stake <- o A..: "stake"
          vrfOutput <- o A..: "vrfOutput"
          preferredChain <- o A..: "preferredChain"
          downstreams <- o A..: "downstreams"
          pure NodeState{..}

instance A.ToJSON t => A.ToJSON (NodeState t) where
  toJSON NodeState{..} =
    A.object
      [
        "nodeId" A..= nodeId
      , "protocol" A..= protocol
      , "clock" A..= clock
      , "slot" A..= slot
      , "stake" A..= stake
      , "vrfOutput" A..= vrfOutput
      , "preferredChain" A..= preferredChain
      , "downstreams" A..= downstreams
      ]

data NodeProcess t m =
  NodeProcess
  {
    incoming :: TQueue m (InEnvelope t)
  , outgoing :: TQueue m (OutEnvelope t)
  }
    deriving stock (Generic)
