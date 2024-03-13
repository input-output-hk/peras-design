-- | Defines the events emitted by a simulation that are relevant for analysing the results.
module Peras.Event where

import Control.Monad.Class.MonadTime (NominalDiffTime)
import Data.Aeson (Value)
import Data.ByteString (ByteString)
import Data.Time (UTCTime)
import Numeric.Natural (Natural)
import Peras.Block (Slot)
import Peras.Message (Message, NodeId)

newtype UniqueId = UniqueId {uniqueId :: ByteString}

type ByteSize = Natural

type CpuTime = NominalDiffTime

data Event
  = Send
      { uuid :: UniqueId
      , timestamp :: UTCTime
      , from :: NodeId
      , to :: NodeId
      , payload :: Message
      , txBytes :: ByteSize
      }
  | Drop
      { uuid :: UniqueId
      , timestamp :: UTCTime
      , from :: NodeId
      , to :: NodeId
      , payload :: Message
      , txBytes :: ByteSize
      }
  | Receive
      { uuid :: UniqueId
      , timestamp :: UTCTime
      , from :: NodeId
      , to :: NodeId
      , payload :: Message
      , rxBytes :: ByteSize
      }
  | SlotLeader
      { self :: NodeId
      , slot :: Slot
      }
  | CommitteeMember
      { self :: NodeId
      , slot :: Slot
      }
  | Rolledback
      { self :: NodeId
      , rollback :: Rollback
      }
  | Compute
      { self :: NodeId
      , cpuTime :: CpuTime
      }
  | Trace Value

data Rollback = Rollback
  { atSlot :: Slot
  , slotsRolledBack :: Natural
  , blocksRolledBack :: Natural
  , fromWeight :: Double
  , toWeight :: Double
  }
