module Peras.Message where

open import Data.String using (String)

open import Peras.Block using (Block; Slot)
open import Peras.Chain using (Chain; RoundNumber; Vote)

record NodeId : Set where
  constructor MkNodeId
  field
    nodeId : String

open NodeId public

{-# COMPILE AGDA2HS NodeId #-}

-- | Message exchanged between nodes.
--
-- We do not separate messages between inputs and outputs as, by
-- definition, a message /output/ by one node is an /input/ to some
-- other node.  The routing should be handled by the networking layer
-- interposed between all the nodes.
data Message : Set where

  -- | New slot occurs (represents the passage of time)
  NextSlot : Slot → Message

  -- | Some `Block` is received from upstream or broadcast
  -- downstream.
  SomeBlock : Block → Message

  -- | Best chain has changed.
  NewChain : Chain → Message

{-# COMPILE AGDA2HS Message #-}
