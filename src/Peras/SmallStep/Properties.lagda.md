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

open import Peras.Block using (PartyId; Honesty; Block; Slot; Tx; PartyIdO; Certificate)
open import Peras.Chain using (RoundNumber; Vote)
open import Peras.Crypto
open import Peras.Params using (Params)

open import Data.Tree.AVL.Map PartyIdO as M using (Map; lookup; insert; empty)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; subst; trans)
```
-->

```agda
module _ {block₀ : Block} {cert₀ : Certificate}
         (IsCommitteeMember : PartyId → RoundNumber → MembershipProof → Set)
         (IsVoteSignature : Vote → Signature → Set)
         (IsSlotLeader : PartyId → Slot → LeadershipProof → Set)
         (IsBlockSignature : Block → Signature → Set)
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
           (txSelection : Slot → PartyId → List Tx)
           (parties : List PartyId)
           where

    open import Data.List.Relation.Binary.Subset.Propositional {A = Block} using (_⊆_)
    open import Peras.SmallStep using (Stateˡ; Stateᵍ; _↝_; _↝⋆_; ⟪_⟫; CollisionFree; ForgingFree)
```
```agda
    module _ ⦃ N₀ : Stateᵍ ⦄ where

      open TreeType
      open Stateᵍ
```
### Knowledge propagation

The lemma describes how knowledge is propagated between honest parties in the system.

```agda
      postulate
        knowledge-propagation : ∀ {N₁ N₂ : Stateᵍ {block₀} {cert₀} {IsCommitteeMember} {IsVoteSignature} {IsSlotLeader} {IsBlockSignature} {A} {blockTree} {AdversarialState} {adversarialState₀} {txSelection} {parties}}
          → {p₁ p₂ : PartyId}
          → {t₁ t₂ : A}
          → N₀ ↝ N₁
          → N₁ ↝ N₂
          → lookup (stateMap N₁) p₁ ≡ just ⟪ t₁ ⟫
          → lookup (stateMap N₁) p₂ ≡ just ⟪ t₂ ⟫
          → clock N₁ ≡ clock N₂
          → allBlocks blockTree t₁ ⊆ allBlocks blockTree t₂
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
        chain-growth : ∀ {N₁ N₂ : Stateᵍ}
          → {p₁ p₂ : PartyId}
          → {h₁ : Honesty p₁} {h₂ : Honesty p₂}
          → {d₁ d₂ : List Vote}
          → {t₁ t₂ : A}
          → {w : ℕ}
          → let c₁ = bestChain blockTree ((clock N₁) ∸ 1) t₁
                c₂ = bestChain blockTree ((clock N₂) ∸ 1) t₂
                cs₁ = certs blockTree t₁ c₁
                cs₂ = certs blockTree t₂ c₂
            in
            h₁ ≡ Honest {p₁}
          → h₂ ≡ Honest {p₂}
          → N₀ ↝ N₁
          → N₁ ↝ N₂
          → lookup (stateMap N₁) p₁ ≡ just ⟪ t₁ ⟫
          → lookup (stateMap N₁) p₂ ≡ just ⟪ t₂ ⟫
          → luckySlots (clock N₁ , clock N₂) ≥ w
          → ∥ c₁ , cs₁ ∥ + w ≤ ∥ c₂ , cs₂ ∥
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
        common-prefix : ∀ {N : Stateᵍ}
          → {p : PartyId} {h : Honesty p} {c : Chain} {k : Slot} {bh : List Block} {t : A}
          → lookup (stateMap N) p ≡ just ⟪ t ⟫
          → N₀ ↝ N
          → ForgingFree N
          → CollisionFree N
          → h ≡ Honest {p}
          → let sl = clock N
            in (prune k (bestChain blockTree (sl ∸ 1) t)) ⪯ c
             ⊎ (Σ[ sl′ ∈ Slot ] (sl′ < k × superSlots (sl′ , sl) < 2 * adversarialSlots (sl′ , sl)))
```
## Timed common prefix

```agda

```
