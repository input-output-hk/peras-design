module Peras.Message where

import Peras.Block (Block, Slot)
import Peras.Chain (Chain)

data NodeId = MkNodeId {nodeId :: String}

data Message votes
  = NextSlot Slot
  | SomeBlock (Block votes)
  | NewChain (Chain votes)
