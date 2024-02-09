{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Peras.Block where

import Data.ByteString as BS
import Numeric.Natural (Natural)

newtype PartyId = PartyId {unPartyId :: ByteString}
  deriving (Eq, Show, Ord)

newtype BlockId = BlockId {unBlockId :: ByteString}
  deriving (Eq, Show, Ord)

newtype Slot = Slot Natural
  deriving (Eq, Show, Num, Enum, Real, Ord, Integral)

data Block t = Block
  { blockId :: BlockId
  , slotNumber :: Slot
  , creatorId :: PartyId
  , parentBlock :: BlockId
  , includedVotes :: t
  , payload :: ByteString
  }
  deriving (Eq, Show, Ord)
