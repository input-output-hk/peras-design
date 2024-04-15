module CommonTypes where

import GHC.Generics

data Party
  = Alice
  | Bob
  deriving (Eq, Ord, Show, Generic)

type BlockIndex = Integer
type Slot = Integer

data Block = Blk {blockIndex :: BlockIndex}
  deriving (Eq, Ord, Show, Generic)
