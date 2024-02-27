module Peras.Message where

import Peras.Block (Block, Slot)
import Peras.Chain (Chain)

data NodeId = MkNodeId {nodeId :: String}

data Message
  = NextSlot Slot
  | SomeBlock Block
  | NewChain Chain
