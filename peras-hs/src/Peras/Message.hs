module Peras.Message where

import Peras.Block (Block, Slot)
import Peras.Chain (Chain, Vote)

newtype NodeId = MkNodeId {nodeId :: String}
  deriving (Eq, Ord, Read, Show)

data Message a
  = NextSlot Slot
  | SomeBlock Block
  | NewChain Chain
  | SomeVote (Vote a)
