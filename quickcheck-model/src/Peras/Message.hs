{-# LANGUAGE LambdaCase #-}

module Peras.Message where

import Data.ByteString (ByteString)
import Data.Maybe (mapMaybe)
import Peras.Block (Block, BlockId, Slot)

newtype NodeId = NodeId {nodeId :: ByteString}
  deriving (Eq, Show, Ord)

data Message votes
  = NextSlot Slot
  | RollForward (Block votes)
  | RollBack BlockId
  deriving (Eq, Show)

selectBlocks :: [Message ()] -> [Block ()]
selectBlocks = mapMaybe isRollForward

isRollForward :: Message () -> Maybe (Block ())
isRollForward = \case
  RollForward block -> Just block
  _other -> Nothing
