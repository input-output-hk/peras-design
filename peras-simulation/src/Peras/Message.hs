module Peras.Message where

import Peras.Block (Block, BlockBody, Certificate)
import Peras.Chain (Chain, Vote)
import Peras.Crypto (Hash)
import Peras.Numbering (SlotNumber)

newtype NodeId = MkNodeId {nodeId :: String}
  deriving (Eq, Ord, Read, Show)

data Message
  = NextSlot SlotNumber
  | NewChain Chain
  | SomeVote Vote
  | SomeCertificate Certificate
  | FetchVotes [Hash Vote]
  | FollowChain (Hash Chain)
  | RollForward Block
  | RollBack Block
  | FetchBlocks [Hash Block]
  | SomeBlock BlockBody
