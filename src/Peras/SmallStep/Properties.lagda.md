```agda
module Peras.SmallStep.Properties where
```

<!--
```agda
open import Data.Bool using (Bool)
open import Data.List using (List)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; _∸_; _<_; _≤_; _≥_; _*_; _+_)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)

open import Peras.Block using (PartyId; Honesty; Block; Slot; Tx; PartyIdO)
open import Peras.Chain using (RoundNumber; Vote)
open import Peras.Crypto using (Hashable)
open import Peras.Params using (Params)

open import Data.Tree.AVL.Map PartyIdO as M using (Map; lookup; insert; empty)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; subst; trans)
```
-->

```agda
module _ {block₀ : Block}
         ⦃ _ : Hashable Block ⦄
         ⦃ _ : Hashable Vote ⦄
         ⦃ _ : Hashable (List Tx) ⦄
         ⦃ _ : Params ⦄
         where

  open Hashable ⦃...⦄
  open import Peras.SmallStep using (TreeType)

  module _ {A : Set}
           (blockTree : TreeType A)
           {AdversarialState : Set}
           (adversarialState₀ : AdversarialState)
           (isSlotLeader : PartyId → Slot → Bool)
           (isCommitteeMember : PartyId → RoundNumber → Bool)
           (txSelection : Slot → PartyId → List Tx)
           (parties : List PartyId)
           where

    open import Data.List.Relation.Binary.Subset.Propositional {A = Block} using (_⊆_)
    open import Peras.SmallStep using (Stateˡ; Stateᵍ; _↝_; _↝⋆_; ⟪_,_⟫; CollisionFree; ForgingFree)
```
```agda
    module _ ⦃ N₀ : Stateᵍ ⦄ where

      open TreeType
      open Stateᵍ
```
### Knowledge propagation

The lemma describes how knowledge is propagated between honest parties in the system.
TODO: Do we the result as well for votes? I.e. `(allVotes blockTree) t₁ ⊆ (allVotes blockTree) t₂`

```agda
      postulate
        kownledge-propagation : ∀ {N₁ N₂ : Stateᵍ {block₀} {A} {blockTree} {AdversarialState} {adversarialState₀} {isSlotLeader} {isCommitteeMember} {txSelection} {parties}}
          → {p₁ p₂ : PartyId}
          → {d₁ d₂ : List Vote}
          → {t₁ t₂ : A}
          → N₀ ↝ N₁
          → N₁ ↝ N₂
          → lookup (stateMap N₁) p₁ ≡ just ⟪ t₁ , d₁ ⟫
          → lookup (stateMap N₁) p₂ ≡ just ⟪ t₂ , d₂ ⟫
          → clock N₁ ≡ clock N₂
          → (allBlocks blockTree) t₁ ⊆ (allBlocks blockTree) t₂
```

```agda
      open import Data.Sum using (_⊎_; inj₁; inj₂)
      open import Peras.Chain
      open Honesty

      postulate
        luckySlots : Slot × Slot → ℕ
        superSlots : Slot × Slot → ℕ
        adversarialSlots : Slot × Slot → ℕ
```
## Chain growth

The chain growth property informally says that in each period, the best chain of any honest
party will increase at least by a number that is proportional to the number of lucky slots in
that period.

```agda
      postulate
        chain-growth : ∀ {N₁ N₂ : Stateᵍ {block₀} {A} {blockTree} {AdversarialState} {adversarialState₀} {isSlotLeader} {isCommitteeMember} {txSelection} {parties}}
          → {p₁ p₂ : PartyId}
          → {h₁ : Honesty p₁} {h₂ : Honesty p₂}
          → {c₁ c₂ : Chain}
          → {d₁ d₂ : List Vote}
          → {pr₁ : DanglingVotes c₁ d₁}
          → {pr₂ : DanglingVotes c₂ d₂}
          → {t₁ t₂ : A}
          → {w : ℕ}
          → h₁ ≡ Honest {p₁}
          → h₂ ≡ Honest {p₂}
          → N₀ ↝ N₁
          → N₁ ↝ N₂
          → lookup (stateMap N₁) p₁ ≡ just ⟪ t₁ , d₁ ⟫
          → lookup (stateMap N₁) p₂ ≡ just ⟪ t₂ , d₂ ⟫
          → luckySlots (clock N₁ , clock N₂) ≥ w
          → c₁ ≡ ((bestChain blockTree) ((clock N₁) ∸ 1) d₁ t₁)
          → c₂ ≡ ((bestChain blockTree) ((clock N₂) ∸ 1) d₂ t₂)
          → ∥ ⟨ c₁ , d₁ , pr₁ ⟩ ∥ + w ≤ ∥ ⟨ c₂ , d₂ , pr₂ ⟩ ∥
```

## Chain quality

The chain quality property informally says that within any chunk of consecutive blocks in an
honest party's best chain, there is an honest share of blocks. This share is proportional to
the difference between the number of honest and adversarial slots.

```agda

```

## Common prefix

The common prefix property informally says that during the execution of the protocol the
chains of honest parties will always be a common prefix of each other.

```agda
      postulate
        common-prefix : ∀ {N : Stateᵍ {block₀} {A} {blockTree} {AdversarialState} {adversarialState₀} {isSlotLeader} {isCommitteeMember} {txSelection} {parties}}
          → {p : PartyId} {h : Honesty p} {c : Chain} {k : Slot} {bh : List Block} {t : A} {d : List Vote}
          → lookup (stateMap N) p ≡ just ⟪ t , d ⟫
          → N₀ ↝ N
          → ForgingFree N
          → CollisionFree N
          → h ≡ Honest {p}
          → let sl = clock N
            in (prune k ((bestChain blockTree) (sl ∸ 1) d t)) ⪯ c
             ⊎ (Σ[ sl′ ∈ Slot ] (sl′ < k × superSlots (sl′ , sl) < 2 * adversarialSlots (sl′ , sl)))
```
## Timed common prefix

```agda

```
