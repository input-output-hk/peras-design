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
  rollbacks,
  owner,
  activeVotes,
  preferredChain,
  initialSeed,
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
import Peras.IOSim.Types (Coin, Rollback, Votes)
import Peras.Message (NodeId)
import Peras.Orphans ()

import qualified Data.Aeson as A
import qualified Data.Set as S

data NodeState = NodeState
  { _nodeId :: NodeId
  , _owner :: PartyId
  , _initialSeed :: Int
  , _clock :: UTCTime
  , _slot :: Slot
  , _stake :: Coin
  , _vrfOutput :: Double
  , _preferredChain :: Chain Votes
  , _activeVotes :: Votes
  , _downstreams :: S.Set NodeId
  , _slotLeader :: Bool
  , _committeeMember :: Bool
  , _rollbacks :: [Rollback]
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance A.FromJSON NodeState where
  parseJSON =
    A.withObject "NodeState" $
      \o ->
        do
          _nodeId <- o A..: "nodeId"
          _owner <- o A..: "owner"
          _initialSeed <- o A..: "randomSeed"
          _clock <- o A..: "clock"
          _slot <- o A..: "slot"
          _stake <- o A..: "stake"
          _vrfOutput <- o A..: "vrfOutput"
          _preferredChain <- o A..: "preferredChain"
          _activeVotes <- o A..: "activeVotes"
          _downstreams <- o A..: "downstreams"
          _slotLeader <- o A..: "slotLeader"
          _committeeMember <- o A..: "committeeMember"
          _rollbacks <- o A..: "rollbacks"
          pure NodeState{..}

instance A.ToJSON NodeState where
  toJSON NodeState{..} =
    A.object
      [ "nodeId" A..= _nodeId
      , "owner" A..= _owner
      , "randomSeed" A..= _initialSeed
      , "clock" A..= _clock
      , "slot" A..= _slot
      , "stake" A..= _stake
      , "vrfOutput" A..= _vrfOutput
      , "preferredChain" A..= _preferredChain
      , "activeVotes" A..= _activeVotes
      , "downstreams" A..= _downstreams
      , "slotLeader" A..= _slotLeader
      , "committeeMember" A..= _committeeMember
      , "rollbacks" A..= _rollbacks
      ]

makeLenses ''NodeState
