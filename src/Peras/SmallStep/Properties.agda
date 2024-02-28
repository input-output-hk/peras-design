module Peras.SmallStep.Properties where

open import Data.Bool using (Bool)
open import Data.List using (List)
open import Data.Maybe using (just)

open import Peras.Block using (PartyId; Honesty; Block; Slot; Tx; PartyIdO)
open import Peras.Crypto using (Hash)

open import Data.Tree.AVL.Map PartyIdO as M using (Map; lookup; insert; empty)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; subst; trans)

module _ {block₀ : Block}
         {_♯ : Block → Hash}
         where

  open import Peras.SmallStep using (TreeType)

  module _ {T : Set}
           (blockTree : TreeType {block₀} {_♯} T)
           (honest? : (p : PartyId) → Honesty p)
           (lottery : PartyId → Slot → Bool)
           (txSelection : Slot → PartyId → List Tx)
           where

    open import Data.List.Relation.Binary.Subset.Propositional {A = Block} using (_⊆_)

    open import Peras.SmallStep using (Stateˡ; Stateᵍ; _↝_; _↝⋆_; Progress; progress; N₀; ⟨_,_⟩)

    open Progress
    open TreeType
    open Stateᵍ

    -- knowledge propagation
    postulate
      lemma1 : ∀ {N₁ N₂ : Stateᵍ {block₀} {_♯} {T} {blockTree} {honest?} {lottery} {txSelection}}
        → {p₁ p₂ : PartyId}
        → {t₁ t₂ : T}
        → N₀ ↝ N₁
        → N₁ ↝ N₂
        → progress N₁ ≡ Ready
        → progress N₂ ≡ Delivered
        → lookup (stateMap N₁) p₁ ≡ just ⟨ p₁ , t₁ ⟩
        → lookup (stateMap N₁) p₂ ≡ just ⟨ p₂ , t₂ ⟩
        → clock N₁ ≡ clock N₂
        → (allBlocks blockTree) t₁ ⊆ (allBlocks blockTree) t₂

    {- From the paper:

    Proof sketch. Our main observation is that at any point in time a block is in the tree of p1, it is
    either also already in p2’s tree or to be delivered at the next delivery transition.

    Blocks can be added when an honest party wins the right to bake a block, in which case they will immediately
    send the block to all other parties and thus fulfill the invariant, or they can be added by an
    adversary and thereby delivered to an honest party by a delivery event, in which case it will be
    delivered to all other honest parties in the following delivery slot (by our network assumption).

    This is in particular true when p1 and p2 is at Ready, which means that after the delivery
    transition p2 will know all the blocks that p1 knew before.
    -}
