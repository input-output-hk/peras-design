{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Node.Types (
  NodeState(..)
) where

import Control.Monad.Class.MonadTime (UTCTime)
import GHC.Generics (Generic)
import Peras.Block (Slot)
import Peras.Chain (Chain)
import Peras.IOSim.Types (Currency)
import Peras.Message(NodeId)
import Peras.Orphans ()

import qualified Data.Aeson as A
import qualified Data.Set as S

data NodeState v =
  NodeState
  {
    nodeId :: NodeId
  , clock :: UTCTime
  , slot :: Slot
  , stake :: Currency
  , vrfOutput :: Double
  , preferredChain :: Chain v
  , downstreams :: S.Set NodeId
  }
    deriving stock (Eq, Generic, Ord, Read, Show)

instance A.FromJSON v => A.FromJSON (NodeState v) where
  parseJSON =
    A.withObject "NodeState"
      $ \o ->
        do
          nodeId <- o A..: "nodeId"
          clock <- o A..: "clock"
          slot <- o A..: "slot"
          stake <- o A..: "stake"
          vrfOutput <- o A..: "vrfOutput"
          preferredChain <- o A..: "preferredChain"
          downstreams <- o A..: "downstreams"
          pure NodeState{..}

instance A.ToJSON v => A.ToJSON (NodeState v) where
  toJSON NodeState{..} =
    A.object
      [
        "nodeId" A..= nodeId
      , "clock" A..= clock
      , "slot" A..= slot
      , "stake" A..= stake
      , "vrfOutput" A..= vrfOutput
      , "preferredChain" A..= preferredChain
      , "downstreams" A..= downstreams
      ]
