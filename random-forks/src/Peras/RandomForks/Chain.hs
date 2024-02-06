{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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

import Data.UUID.V4 (nextRandom)
import Peras.RandomForks.Types (BlockId, PeerName, Slot)

data Block =
  Block
  {
    creator :: PeerName
  , slot :: Slot
  , blockId :: BlockId
  }
    deriving (Eq, Ord, Read, Show)

mkBlock
  :: PeerName
  -> Slot
  -> IO Block
mkBlock name slot = Block name slot <$> nextRandom

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
extendChain block = Chain block

data Message =
  Message
  {
    messageSlot :: Slot
  , messageChain :: Chain
  , messageDestination :: PeerName
  }
    deriving (Eq, Ord, Read, Show)
