{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Node.Types (
  NodeContext (..),
  NodeResult (..),
  NodeStats (..),
  PerasNode (..),
  StepResult (..),
  TraceReport (..),
  TraceSelf,
  hoistNodeContext,
) where

import Control.Monad.Class.MonadTime (UTCTime)
import Data.Aeson (FromJSON, ToJSON, Value)
import Data.Function (on)
import Data.List (nub)
import Data.Set (Set)
import GHC.Generics (Generic)
import Generic.Random (genericArbitrary, uniform)
import Peras.Arbitraries ()
import Peras.Block (Block, PartyId)
import Peras.Chain (Chain, Vote)
import Peras.Event (ByteSize, CpuTime, Event, Rollback)
import Peras.IOSim.Hash (BlockHash, VoteHash)
import Peras.IOSim.Message.Types (InEnvelope, OutEnvelope)
import Peras.IOSim.Protocol.Types (Protocol)
import Peras.IOSim.Types (Coin, simulationStart)
import Peras.Message (NodeId)
import Peras.Numbering (RoundNumber, SlotNumber)
import Peras.Orphans ()
import Test.QuickCheck (Arbitrary (..))
import Test.QuickCheck.Instances.Time ()

import qualified Data.Map as M

type TraceSelf m = Value -> m ()

data NodeContext m = NodeContext
  { protocol :: Protocol
  , totalStake :: Coin
  , slot :: SlotNumber
  , clock :: UTCTime
  , traceSelf :: TraceSelf m
  }

hoistNodeContext :: (forall a. m a -> n a) -> NodeContext m -> NodeContext n
hoistNodeContext f NodeContext{..} = NodeContext{traceSelf = f . traceSelf, ..}

data NodeStats = NodeStats
  { preferredTip :: [(SlotNumber, BlockHash)]
  , rollbacks :: [Rollback]
  , slotLeader :: [SlotNumber]
  , committeeMember :: [SlotNumber]
  , votingAllowed :: [(RoundNumber, BlockHash)]
  , cpuTime :: CpuTime
  , rxBytes :: ByteSize
  , txBytes :: ByteSize
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON NodeStats
instance ToJSON NodeStats

instance Semigroup NodeStats where
  x <> y =
    NodeStats
      { preferredTip = nub $ on (<>) preferredTip x y
      , rollbacks = nub $ on (<>) rollbacks x y
      , slotLeader = nub $ on (<>) slotLeader x y
      , committeeMember = nub $ on (<>) committeeMember x y
      , votingAllowed = nub $ on (<>) votingAllowed x y
      , cpuTime = on (+) cpuTime x y
      , rxBytes = on (+) rxBytes x y
      , txBytes = on (+) txBytes x y
      }

instance Monoid NodeStats where
  mempty = NodeStats mempty mempty mempty mempty mempty 0 0 0

instance Arbitrary NodeStats where
  arbitrary = genericArbitrary uniform

data TraceReport
  = TraceValue
      { self :: NodeId
      , slot :: SlotNumber
      , clock :: UTCTime
      , value :: Value
      }
  | TraceStats
      { self :: NodeId
      , slot :: SlotNumber
      , clock :: UTCTime
      , statistics :: NodeStats
      }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON TraceReport
instance ToJSON TraceReport

data NodeResult = NodeResult
  { wakeup :: UTCTime
  , outputs :: [OutEnvelope]
  , stats :: NodeStats
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON NodeResult
instance ToJSON NodeResult

instance Semigroup NodeResult where
  x <> y =
    NodeResult
      { wakeup = on min wakeup x y -- FIXME: This isn't precisely correct.
      , outputs = on (<>) outputs x y
      , stats = on (<>) stats x y
      }

instance Monoid NodeResult where
  mempty = NodeResult simulationStart mempty mempty

instance Arbitrary NodeResult where
  arbitrary = genericArbitrary uniform

class PerasNode a where
  getNodeId :: a -> NodeId
  getOwner :: a -> PartyId
  getStake :: a -> Coin
  setStake :: a -> Coin -> a
  getDownstreams :: a -> Set NodeId
  getPreferredChain :: a -> Chain
  getBlocks :: a -> M.Map BlockHash Block
  getVotes :: a -> M.Map VoteHash Vote
  handleMessage :: Monad m => a -> NodeContext m -> InEnvelope -> m (NodeResult, a)
  stop :: Monad m => a -> NodeContext m -> m a

data StepResult = StepResult
  { stepTime :: UTCTime
  , stepOutputs :: [OutEnvelope]
  , stepEvents :: [Event]
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON StepResult
instance ToJSON StepResult
