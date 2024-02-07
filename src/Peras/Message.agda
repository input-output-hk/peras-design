module Peras.Message where

open import Data.String using (String)

open import Peras.Block using (Block; Slot)
open import Peras.Chain using (Chain; RoundNumber; Vote)

data Message msg : Set where
  VoteFor : RoundNumber → msg → Message msg
  NewVote : Vote msg → Message msg
  NewChain : msg → Message msg

record NodeId : Set where
  constructor mkNodeId
  field
    nodeId : String

-- | Messages sent to the node.
data Input : Set where

  -- | New slot occurs (represents the passage of time)
  NextSlot : Slot → Input

  -- | Some `NodeId` has sent a requested `Block` to this node.
  SomeBlock : NodeId → Block → Input

  -- | Some `NodeId` is notifying us their best chain has changed.
  UpdatedChain : NodeId → Chain → Input

{-# COMPILE AGDA2HS Input deriving ( Show, Eq ) #-}

data Output : Set where

  -- | Node needs some block from given `NodeId`.
  FetchBlock : NodeId → Block → Output

  -- | Node changed its best chain
  NewChain : Chain → Output

{-# COMPILE AGDA2HS Output deriving ( Show, Eq ) #-}
