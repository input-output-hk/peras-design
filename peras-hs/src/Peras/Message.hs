module Peras.Message where

import Peras.Block (Block, BlockBody, Certificate, Slot)
import Peras.Chain (Chain, Vote)
import Peras.Crypto (Hash)

newtype NodeId = MkNodeId {nodeId :: String}
  deriving (Eq, Ord, Read, Show)

data Message
  = NextSlot Slot
  | NewChain Chain
  | SomeVote Vote
  | SomeCertificate Certificate
  | FetchVotes [Hash Vote]
  | FollowChain (Hash Chain)
  | RollForward Block
  | RollBack Block
  | FetchBlocks [Hash Block]
  | SomeBlock BlockBody
