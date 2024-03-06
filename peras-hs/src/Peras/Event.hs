-- | Defines the events emitted by a simulation that are relevant for analysing the results.
module Peras.Event where

import Data.Aeson (Value)
import Data.ByteString (ByteString)
import Data.Time (UTCTime)
import Peras.Message (Message, NodeId)

newtype UniqueId = UniqueId ByteString

data Event
  = Send
      { uuid :: UniqueId
      , timestamp :: UTCTime
      , from :: NodeId
      , to :: NodeId
      , payload :: Message
      }
  | Receive
      { uuid :: UniqueId
      , timestamp :: UTCTime
      , from :: NodeId
      , to :: NodeId
      , payload :: Message
      }
  | Trace Value
