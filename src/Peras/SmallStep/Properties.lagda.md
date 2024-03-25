```agda
{-# OPTIONS --allow-unsolved-metas #-}
module Peras.SmallStep.Properties where
```

<!--
```agda
open import Data.Bool using (Bool)
open import Data.List as List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Membership.DecPropositional using (_∈?_)

open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Relation.Unary.Any using (Any; _─_; _∷=_)
open import Data.List.Relation.Unary.Any.Properties using (¬Any[])
open import Data.List.Relation.Unary.All using (All; map)
open import Data.List.Relation.Unary.All.Properties using (¬All⇒Any¬; All¬⇒¬Any; ─⁺; ─⁻)

open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Fin using (zero; suc; _≟_)
open import Data.Fin.Properties using (0≢1+n)
open import Data.Nat as ℕ using (ℕ; _∸_; _<_; _≤_; _≥_; _*_; _+_)
open import Data.Nat.Properties using (n≤1+n; 1+n≰n; ≤-refl; ≤-reflexive; ≤-trans)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)

open import Function.Base using (_∘_; id; _$_; flip)

open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)

open import Peras.Block using (PartyId; Honesty; Block; Slot; Tx; PartyIdO; Certificate)
open import Peras.Chain using (RoundNumber; Vote)
open import Peras.Crypto
open import Peras.Params using (Params)

open import Data.Tree.AVL.Map PartyIdO as M using (Map; lookup; insert; empty; fromList)
open import Data.Tree.AVL.Map.Membership.Propositional PartyIdO
open import Data.Tree.AVL.Map.Membership.Propositional.Properties PartyIdO

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym; subst; trans)
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
    open import Peras.SmallStep
    open TreeType
```
### Initial state
```agda
    LocalState′ = Stateˡ {block₀} {cert₀} {IsCommitteeMember} {IsVoteSignature} {IsSlotLeader} {IsBlockSignature} {A} {blockTree} {AdversarialState} {adversarialState₀} {txSelection} {parties}

    GlobalState = Stateᵍ {block₀} {cert₀} {IsCommitteeMember} {IsVoteSignature} {IsSlotLeader} {IsBlockSignature} {A} {blockTree} {AdversarialState} {adversarialState₀} {txSelection} {parties}

    state₀ : LocalState′
    state₀ = ⟪ tree₀ blockTree ⟫

    states₀ : Map LocalState′
    states₀ = List.foldr (λ { p m → insert p state₀ m }) empty parties

    N₀ : GlobalState
    N₀ = ⟦ 0
         , states₀
         , []
         , []
         , adversarialState₀
         ⟧

    open TreeType
    open Stateᵍ

    postulate
      init-state₀ : ∀ {p}
        → p ∈ parties
        → (p , state₀) ∈ₖᵥ states₀
      -- init-state₀ p∈ps = {!!}

    init-tree₀ : ∀ {p}
      → p ∈ parties
      → lookup (stateMap N₀) p ≡ just ⟪ tree₀ blockTree ⟫
    init-tree₀ = ∈ₖᵥ-lookup⁺ ∘ init-state₀
```
### Knowledge propagation

The lemma describes how knowledge is propagated between honest parties in the system.

```agda
    open Honesty
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Peras.Chain
    open _↝_
```
```agda
    clock-incr : ∀ {M N : GlobalState}
      → M ↝ N
      → clock M ≤ clock N
    clock-incr {⟦ c , _ , _ , _ , _ ⟧} {⟦ c , _ , _ , _ , _ ⟧} (Deliver (honest _ _ _)) = ≤-refl
    clock-incr {⟦ c , _ , _ , _ , _ ⟧} {⟦ c , _ , _ , _ , _ ⟧} (Deliver (corrupt _)) = ≤-refl
    clock-incr {⟦ c , _ , _ , _ , _ ⟧} {⟦ c , _ , _ , _ , _ ⟧} (CastVote _ (honest _ _ _ _ _)) = ≤-refl
    clock-incr {⟦ c , _ , _ , _ , _ ⟧} {⟦ c , _ , _ , _ , _ ⟧} (CreateBlock _ (honest _ _ _ _)) = ≤-refl
    clock-incr {M} (NextSlot _) = n≤1+n (clock M)

    clock-incr⋆ : ∀ {M N : GlobalState}
      → M ↝⋆ N
      → clock M ≤ clock N
    clock-incr⋆ (_ ∎) = ≤-refl
    clock-incr⋆ (_ ↝⟨ x ⟩ x₁) = ≤-trans (clock-incr x) (clock-incr⋆ x₁)

    postulate
      tree-inv : ∀ {p q} {N : GlobalState} {l}
        → p ≢ q
        → lookup (stateMap N) p ≡ lookup (insert q l (stateMap N)) p
```
```agda
    knowledge-propagation₀ : ∀ {N : GlobalState}
      → {p₁ p₂ : PartyId}
      → {t₁ t₂ : A}
      → p₁ ∈ parties
      → p₂ ∈ parties
      → N₀ ↝⋆ N -- needed as precondition for N₁ (starting from empty local states and empty messages)
      → lookup (stateMap N) p₁ ≡ just ⟪ t₁ ⟫
      → lookup (stateMap N) p₂ ≡ just ⟪ t₂ ⟫
      → Delivered N
      → allBlocks blockTree t₁ ⊆ allBlocks blockTree t₂
    knowledge-propagation₀ {N} {p₁} {p₂} p₁∈ps p₂∈ps (_ ∎) x₁ x₂ x₃  =
      let z₁ = just-injective $ trans (sym (init-tree₀ {p₁} p₁∈ps)) x₁
          z₂ = just-injective $ trans (sym (init-tree₀ {p₂} p₂∈ps)) x₂
          a₁ = cong (allBlocks blockTree) (tree-inj refl refl z₁)
          a₂ = cong (allBlocks blockTree) (tree-inj refl refl z₂)
      in ⊆-reflexive (trans (sym a₁) a₂)
    knowledge-propagation₀ _ _ (.N₀ ↝⟨ Deliver (honest {ms = ms} x m∈ms x₆) ⟩ x₅) x₁ x₂ x₃ = contradiction m∈ms ¬Any[]
    knowledge-propagation₀ _ _ (.N₀ ↝⟨ Deliver (corrupt m∈ms) ⟩ x₅) x₁ x₂ x₃ x₄ = contradiction m∈ms ¬Any[]
    knowledge-propagation₀ _ _ (.N₀ ↝⟨ CastVote x x₆ ⟩ x₅) x₁ x₂ x₃ x₄ = {!!} -- votes don't affect allBlocks
    knowledge-propagation₀ _ _ (.N₀ ↝⟨ CreateBlock x x₆ ⟩ x₅) x₁ x₂ x₃ x₄ = {!!} -- CreateBlock : b ∈ t₁ , next slot Receive: b ∈ t₂
    knowledge-propagation₀ _ _ (.N₀ ↝⟨ NextSlot x ⟩ x₅) x₁ x₂ x₃ x₄ = {!!} -- trivial

    knowledge-propagation : ∀ {N₁ N₂ : GlobalState}
      → {p₁ p₂ : PartyId}
      → {t₁ t₂ : A}
      → p₁ ∈ parties
      → p₂ ∈ parties
      → N₀ ↝⋆ N₁ -- needed as precondition for N₁ (starting from empty local states and empty messages)
      → N₁ ↝⋆ N₂
      → lookup (stateMap N₁) p₁ ≡ just ⟪ t₁ ⟫
      → lookup (stateMap N₂) p₂ ≡ just ⟪ t₂ ⟫
      → Delivered N₂
      → clock N₁ ≡ clock N₂
      → allBlocks blockTree t₁ ⊆ allBlocks blockTree t₂

    -- base case
    knowledge-propagation p₁∈p p₂∈p n1 (_ ∎) s₁ s₂ x₄ n₂ = knowledge-propagation₀ p₁∈p p₂∈p n1 s₁ s₂ x₄

    -- Deliver
    knowledge-propagation {N₁} {N₂} {p₁} {p₂} {t₁} {t₂} p₁∈p p₂∈p x (_ ↝⟨ d@(Deliver (honest {p} {lₚ} {lₚ′} {m} x₁ m∈ms x₉)) ⟩ N′↝⋆N₂) N₁×p₁≡t₁ x₃ n₂ x₆ x₇ with p₁ ℕ.≟ p
    ... | no ¬e =    -- adds a block/vote/cert to some p's blocktree
      let xx = tree-inv {p₁} {p} {N₁} {lₚ′} ¬e
          yy = trans (sym xx) N₁×p₁≡t₁
      in knowledge-propagation {p₁ = p₁} p₁∈p p₂∈p (↝∘↝⋆ x d) N′↝⋆N₂ yy x₃ n₂ x₆ x₇

    ... | yes refl -- with b ∈? allBlocks t₂  -- adds a block/vote/cert to p₁'s blocktree
                     -- proof: p₂ either already has the block in the local blocktree or
                     --        it is in the message buffer with delay 0 (honest create in prev slot)
    -- ... | xx = ?
      = knowledge-propagation {p₁ = p₁} p₁∈p p₂∈p (↝∘↝⋆ x d) N′↝⋆N₂ {!!} x₃ n₂ x₆ x₇

    knowledge-propagation p₁∈p p₂∈p x (_ ↝⟨ Deliver (corrupt m∈ms) ⟩ N′↝⋆N₂) x₂ x₃ n₂ x₆ x₇ = {!!} -- potentially adds a block to p₂'s blocktree in the next slot

    -- CastVote
    knowledge-propagation p₁∈p p₂∈p x (_ ↝⟨ d@(CastVote _ (honest x₁ x₉ x₁₀ x₁₁ x₁₂)) ⟩ N′↝⋆N₂) x₂ x₃ n₂ x₆ x₇ =
      let xx = knowledge-propagation p₁∈p p₂∈p (↝∘↝⋆ x d) N′↝⋆N₂ {!!} x₃ n₂ x₆ x₇
      in xx -- cast vote not relevant for allBlocks

    -- CreateBlock
    knowledge-propagation p₁∈p p₂∈p x (_ ↝⟨ CreateBlock _ (honest x₁ x₉ x₁₀ x₁₁) ⟩ N′↝⋆N₂) x₂ x₃ n₂ x₆ x₇ = {!!}

    -- NextSlot
    knowledge-propagation {N₁} {N₂} p₁∈p p₂∈p _ (_ ↝⟨ (NextSlot _) ⟩ N′↝⋆N₂) _ _ _ x₆ _ =
      let 1+c≤c = ≤-trans (≤-reflexive (cong ℕ.suc (sym x₆))) (clock-incr⋆ N′↝⋆N₂)
          1+c≰c = 1+n≰n {clock N₂}
      in contradiction 1+c≤c 1+c≰c
```
## Chain growth


```agda
    postulate
      honest-chain-growth : ∀ {N₁ N₂ : GlobalState}
        → {p₁ p₂ : PartyId}
        → {h₁ : Honesty p₁} {h₂ : Honesty p₂}
        → {t₁ t₂ : A}
        → h₁ ≡ Honest {p₁}
        → h₂ ≡ Honest {p₂}
        → N₀ ↝ N₁
        → N₁ ↝ N₂
        → lookup (stateMap N₁) p₁ ≡ just ⟪ t₁ ⟫
        → lookup (stateMap N₂) p₂ ≡ just ⟪ t₂ ⟫
        → let c₁ = bestChain blockTree ((clock N₁) ∸ 1) t₁
              c₂ = bestChain blockTree ((clock N₂) ∸ 1) t₂
              cs₁ = certs blockTree t₁ c₁
              cs₂ = certs blockTree t₂ c₂
          in ∥ c₁ , cs₁ ∥ ≤ ∥ c₂ , cs₂ ∥
```
```agda
    postulate
      luckySlots : Slot × Slot → ℕ
      superSlots : Slot × Slot → ℕ
      adversarialSlots : Slot × Slot → ℕ
```

The chain growth property informally says that in each period, the best chain of any honest
party will increase at least by a number that is proportional to the number of lucky slots in
that period.

```agda
    postulate
      chain-growth : ∀ {N₁ N₂ : GlobalState}
        → {p₁ p₂ : PartyId}
        → {h₁ : Honesty p₁} {h₂ : Honesty p₂}
        → {t₁ t₂ : A}
        → {w : ℕ}
        → h₁ ≡ Honest {p₁}
        → h₂ ≡ Honest {p₂}
        → N₀ ↝⋆ N₁
        → N₁ ↝⋆ N₂
        → lookup (stateMap N₁) p₁ ≡ just ⟪ t₁ ⟫
        → lookup (stateMap N₂) p₂ ≡ just ⟪ t₂ ⟫
        → luckySlots (clock N₁ , clock N₂) ≥ w
        → let c₁ = bestChain blockTree ((clock N₁) ∸ 1) t₁
              c₂ = bestChain blockTree ((clock N₂) ∸ 1) t₂
              cs₁ = certs blockTree t₁ c₁
              cs₂ = certs blockTree t₂ c₂
          in ∥ c₁ , cs₁ ∥ + w ≤ ∥ c₂ , cs₂ ∥
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
      common-prefix : ∀ {N : GlobalState}
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
