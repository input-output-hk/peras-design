module Peras.SmallStep.Properties where

open import Peras.Block using (PartyId; Honesty)

module _ {T : Set} (honest? : (p : PartyId) → Honesty p) where

  open import Data.List.Relation.Binary.Sublist.Propositional

  -- knowledge propagation
{-
  postulate
    lemma1 : ∀ {N₁ N₂ : GlobalState}
      → {p₁ p₂ : PartyId}
      → {tt₁ tt₂ : TreeType}
      → {t₁ t₂ : T}
      → N₀ ↝⋆ N₁
      → N₁ ↝⋆ N₂
      → progress N₁ ≡ Ready
      → progress N₂ ≡ Delivered
      → stateMap N₁ p₁ ≡ just ⟨ p₁ , t₁ ⟩
      → stateMap N₂ p₂ ≡ just ⟨ p₂ , t₂ ⟩
      → slot N₁ ≡ slot N₂
      → allBlocks tt₁ t₁ ⊆ allBlocks tt₁ t₂
-}
  {- From the paper:

  Proof sketch. Our main observation is that at any point in time a block is in the tree of p1, it is
  either also already in p2’s tree or to be delivered at the next delivery transition.

  Blocks can be added when an honest party wins the right to bake a block, in which case they will immediately
  send the block to all other parties and thus fulfill the invariant, or they can be added by an
  adversary and thereby delivered to an honest party by a delivery event, in which case it will be
  delivered to all other honest parties in the following delivery slot (by our network assumption).

  This is in particular true when p1 and p2 is at Ready, which means that after the delivery
  transition p2 will know all the blocks that p1 knew before.

  lemma1 x (⟪ _ , Ready , _ , _ , _ ⟫ ↝⟨ Deliver ⟩ x₂) refl refl x₃ x₄ refl = {!!}
  lemma1 x (⟪ _ , Ready , _ , _ , _ ⟫ ↝⟨ PermParties ⟩ x₂) refl refl x₃ x₄ refl = {!!}
  lemma1 x (⟪ _ , Ready , _ , _ , _ ⟫ ↝⟨ PermMsgs ⟩ x₂) refl refl x₃ x₄ refl = {!!}
  -}
