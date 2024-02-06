{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}

module Peras.RandomForks.Chain (
  Block(..)
, Chain(..)
, Message(..)
, blocks
, chainLength
, extendChain
, mkBlock
) where

import Peras.RandomForks.Types (BlockId, PeerName, Slot)
import System.Random.Stateful (StatefulGen(uniformShortByteString))

data Block =
  Block
  {
    creator :: PeerName
  , slot :: Slot
  , blockId :: BlockId
  }
    deriving (Eq, Ord, Read, Show)

mkBlock
  :: StatefulGen g m
  => g
  -> PeerName
  -> Slot
  -> m Block
mkBlock gen name slot = Block name slot <$> uniformShortByteString 8 gen

data Chain =
  Chain
  {
    block :: Block,
    prev :: Chain
  }
  | Genesis
  deriving stock (Eq, Ord, Read, Show)

blocks :: Chain -> [Block]
blocks = \case
  Genesis -> []
  Chain {block, prev} -> block : blocks prev

chainLength
  :: Chain
  -> Int
chainLength = \case
  Genesis -> 0
  Chain{prev} -> 1 + chainLength prev

extendChain
  :: Block
  -> Chain
  -> Chain
extendChain = Chain

data Message =
  Message
  {
    messageSlot :: Slot
  , messageChain :: Chain
  , messageDestination :: PeerName
  }
    deriving (Eq, Ord, Read, Show)
