{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}

module Peras.IOSim.Node.Types (
  NodeState (NodeState),
  clock,
  committeeMember,
  downstreams,
  nodeId,
  owner,
  preferredChain,
  slot,
  slotLeader,
  stake,
  vrfOutput,
) where

import Control.Lens (makeLenses)
import Control.Monad.Class.MonadTime (UTCTime)
import GHC.Generics (Generic)
import Peras.Block (PartyId, Slot)
import Peras.Chain (Chain)
import Peras.IOSim.Types (Currency)
import Peras.Message (NodeId)
import Peras.Orphans ()

import qualified Data.Aeson as A
import qualified Data.Set as S

data NodeState v = NodeState
  { _nodeId :: NodeId
  , _owner :: PartyId
  , _clock :: UTCTime
  , _slot :: Slot
  , _stake :: Currency
  , _vrfOutput :: Double
  , _preferredChain :: Chain v
  , _downstreams :: S.Set NodeId
  , _slotLeader :: Bool
  , _committeeMember :: Bool
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance A.FromJSON v => A.FromJSON (NodeState v) where
  parseJSON =
    A.withObject "NodeState" $
      \o ->
        do
          _nodeId <- o A..: "nodeId"
          _owner <- o A..: "owner"
          _clock <- o A..: "clock"
          _slot <- o A..: "slot"
          _stake <- o A..: "stake"
          _vrfOutput <- o A..: "vrfOutput"
          _preferredChain <- o A..: "preferredChain"
          _downstreams <- o A..: "downstreams"
          _slotLeader <- o A..: "slotLeader"
          _committeeMember <- o A..: "committeeMember"
          pure NodeState{..}

instance A.ToJSON v => A.ToJSON (NodeState v) where
  toJSON NodeState{..} =
    A.object
      [ "nodeId" A..= _nodeId
      , "owner" A..= _owner
      , "clock" A..= _clock
      , "slot" A..= _slot
      , "stake" A..= _stake
      , "vrfOutput" A..= _vrfOutput
      , "preferredChain" A..= _preferredChain
      , "downstreams" A..= _downstreams
      , "slotLeader" A..= _slotLeader
      , "committeeMember" A..= _committeeMember
      ]

makeLenses ''NodeState
