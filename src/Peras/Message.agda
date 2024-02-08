module Peras.Message where

open import Data.String using (String)

open import Peras.Block using (Block; Slot)
open import Peras.Chain using (Chain; RoundNumber; Vote)

data Message msg : Set where
  VoteFor : RoundNumber → msg → Message msg
  NewVote : Vote msg → Message msg
  NewChain : msg → Message msg

record NodeId : Set where
  constructor MkNodeId
  field
    nodeId : String

open NodeId public

{-# COMPILE AGDA2HS NodeId #-}

-- | Messages sent to the node.
data Input t : Set where

  -- | New slot occurs (represents the passage of time)
  NextSlot : Slot → Input t

  -- | Some `NodeId` has sent a requested `Block` to this node.
  SomeBlock : NodeId → Block t → Input t

  -- | Some `NodeId` is notifying us their best chain has changed.
  UpdatedChain : NodeId → Chain t → Input t

{-# COMPILE AGDA2HS Input #-}

data Output t : Set where

  -- | Node needs some block from given `NodeId`.
  FetchBlock : NodeId → Block t → Output t

  -- | Node changed its best chain
  NewChain : Chain t → Output t

{-# COMPILE AGDA2HS Output #-}
