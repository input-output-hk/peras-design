-- | Defines the events emitted by a simulation that are relevant for analysing the results.
module Peras.Event where

import Control.Monad.Class.MonadTime (NominalDiffTime)
import Data.Aeson (Value)
import Data.ByteString (ByteString)
import Data.Time (UTCTime)
import Peras.Message (Message, NodeId)
import Peras.Numbering (SlotNumber)

newtype UniqueId = UniqueId {uniqueId :: ByteString}

type ByteSize = Integer

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
      , slot :: SlotNumber
      }
  | CommitteeMember
      { self :: NodeId
      , slot :: SlotNumber
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
  { atSlot :: SlotNumber
  , slotsRolledBack :: Integer
  , blocksRolledBack :: Integer
  , fromWeight :: Double
  , toWeight :: Double
  }
