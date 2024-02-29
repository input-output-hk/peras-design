module Peras.Message where

import Peras.Block (Block, Slot)
import Peras.Chain (Chain, Vote)

data NodeId = MkNodeId {nodeId :: String}

data Message a
  = NextSlot Slot
  | SomeBlock Block
  | NewChain Chain
  | SomeVote (Vote a)
