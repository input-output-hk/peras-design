{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TemplateHaskell #-}

module Peras.IOSim.Node.Types (
  NodeState (NodeState),
  chainState,
  clock,
  committeeMember,
  downstreams,
  initialSeed,
  nodeId,
  owner,
  rollbacks,
  rxBytes,
  slot,
  slotLeader,
  stake,
  txBytes,
  vrfOutput,
) where

import Control.Lens (makeLenses)
import Control.Monad.Class.MonadTime (UTCTime)
import Data.Aeson (FromJSON, ToJSON)
import Data.Set (Set)
import Data.Word (Word64)
import GHC.Generics (Generic)
import Generic.Random (genericArbitrary, uniform)
import Peras.Arbitraries ()
import Peras.Block (PartyId, Slot)
import Peras.IOSim.Chain.Types (ChainState)
import Peras.IOSim.Types (Coin, Rollback)
import Peras.Message (NodeId)
import Peras.Orphans ()
import Test.QuickCheck (Arbitrary (..))
import Test.QuickCheck.Instances.Time ()

data NodeState = NodeState
  { _nodeId :: NodeId
  , _owner :: PartyId
  , _initialSeed :: Int
  , _clock :: UTCTime
  , _slot :: Slot
  , _stake :: Coin
  , _vrfOutput :: Double
  , _chainState :: ChainState
  , _downstreams :: Set NodeId
  , _slotLeader :: Bool
  , _committeeMember :: Bool
  , _rollbacks :: [Rollback]
  , _rxBytes :: Word64
  , _txBytes :: Word64
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON NodeState
instance ToJSON NodeState

instance Arbitrary NodeState where
  arbitrary = genericArbitrary uniform

makeLenses ''NodeState
