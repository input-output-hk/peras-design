module Peras.Message where

import Peras.Block (Block, BlockBody, Slot)
import Peras.Chain (Chain, Vote)
import Peras.Crypto (Hash)

newtype NodeId = MkNodeId {nodeId :: String}
  deriving (Eq, Ord, Read, Show)

data Message
  = NextSlot Slot
  | NewChain Chain
  | SomeVote Vote
  | FetchVotes [Hash]
  | FollowChain Block
  | RollForward Block
  | RollBack Block
  | FetchBlocks [Hash]
  | SomeBlock BlockBody
