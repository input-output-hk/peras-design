{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

module Peras.IOSim.Types (
  Block(..)
, BlockHash
, Chain(..)
, NodeId
, RoundNo
, Size
, SlotNo
) where

import GHC.Generics (Generic)

type SlotNo = Int

type BlockHash = String

type RoundNo = Int

type NodeId = String

type Size = Int

data Block =
  Block
  {
    slotNo :: SlotNo
  , hash :: BlockHash
  , size :: Size
  }
    deriving stock (Eq, Generic, Ord, Read, Show)

data Chain =
    Genesis
  | Chain
    {
      block :: Block
    , previous :: Chain
    }
    deriving stock (Eq, Generic, Ord, Read, Show)
