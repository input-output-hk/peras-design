module Peras.QCD.Node.Preagreement where

open import Data.Nat using (ℕ)
open import Haskell.Prelude
open import Peras.QCD.Node.Model
open import Peras.QCD.Protocol
open import Peras.QCD.State
open import Peras.QCD.Types
open import Peras.QCD.Types.Instances
open import Peras.QCD.Util

{-# FOREIGN AGDA2HS
import Peras.QCD.Types.Instances ()
#-}

-- Select a block to vote for, using preagreement.
preagreement : NodeState (Maybe Block)
preagreement =
  do
    -- Fetch the cutoff window for block selection.
    l ← peras L
    -- Fetch the current slot.
    now ← use currentSlot
    -- Find the newest block older than the cutoff window.
    use preferredChain               -- Fetch the prefered chain.
      ⇉ dropWhile (newerThan l now)  -- Ignore the blocks that in the cutoff window.
      ⇉ foundBlock                   -- Report the newest block found, if any.
  where
    -- Check if a block is newer than a specified window.
    newerThan : ℕ → Slot → Block → Bool
    newerThan l now block = slot block + l > now
    -- Report the newest block in a list, if there exists any.
    foundBlock : List Block → Maybe Block
    foundBlock [] = Nothing
    foundBlock (block ∷ _) = Just block
{-# COMPILE AGDA2HS preagreement #-}

