{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

module Peras.IOSim.Message.Types (
  InEnvelope(..)
, Message(..)
, OutEnvelope(..)
) where

import Control.Monad.Class.MonadTime (UTCTime)
import GHC.Generics (Generic)
import Peras.IOSim.Types (Chain, NodeId, Size, SlotNo)

data Message =
  Message
  {
    sender :: NodeId
  , newChain :: Chain
  }
    deriving stock (Eq, Generic, Ord, Read, Show)

data InEnvelope =
    InEnvelope
    {
      message :: Message
    }
  | NewSlot
    {
      slotNo :: SlotNo
    }
  | Stop
    deriving stock (Eq, Generic, Ord, Read, Show)

data OutEnvelope =
    OutEnvelope
    {
      timestamp :: UTCTime
    , outBytes :: Size
    , outMessage :: Message
    , destination :: NodeId
    }
  | Idle
    {
      timestamp :: UTCTime
    }
    deriving stock (Eq, Generic, Ord, Read, Show)
