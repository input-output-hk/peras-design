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

open import Peras.Block as Block using (PartyId; Honesty; Block; Slot; Tx; PartyIdO; Certificate; _≟-Block_)
open import Peras.Chain using (RoundNumber; Vote)
open import Peras.Crypto
open import Peras.Params using (Params)

open import Data.List.Membership.DecPropositional _≟-Block_ using (_∈?_)

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
```
### Knowledge propagation

The lemma describes how knowledge is propagated between honest parties in the system.

<!--
```agda
{-
    block-message : ∀ {N N₁ N₂ : GlobalState} {p} {b} {d} {m} {c}
      → (s : N₀ ↝⋆ N)
      → ⦅ p , BlockMsg b , d ⦆ ∈ messages N
      → Σ[ (s₀ , s₁ , s₂) ∈ ((N₀ ↝⋆ N₁) × (N₁ ↝ N₂) × (N₂ ↝⋆ N)) ]
              (s  ≡ (↝⋆∘↝⋆ s₀ (_ ↝⟨ s₁ ⟩ s₂))
            × (s₁ ≡ CreateBlock {p = p} {Honest {p}} m c))
    block-message s x = ({!!} , {!!} , {!!}) , ({!!} , {!!})
-}
{-
    message-parties : ∀ {N : GlobalState} {p₁ p₂ : PartyId} {t₂ : A} {b : Block} {d}
      → N₀ ↝⋆ N
      → ⦅ p₁ , BlockMsg b , d ⦆ ∈ messages N
      → lookup (stateMap N) p₂ ≡ just ⟪ t₂ ⟫
      → ⦅ p₂ , BlockMsg b , d ⦆ ∈ messages N
         ⊎ b ∈ allBlocks blockTree t₂
    message-parties {N} {p₁} {p₂} {t₂} {b} n m∈ms x₁ with b ∈? allBlocks blockTree t₂
    ... | yes b∈t₂ = inj₂ b∈t₂
    ... | no b∉t₂ =
      let xx = block-message n m∈ms
      in inj₁ {!!}
-}

    open IsTreeType
```
-->
```agda
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
-- TODO      → N₁ ≢ N₂
      → allBlocks blockTree t₁ ⊆ allBlocks blockTree t₂
```
#### base case
```agda
    knowledge-propagation p₁∈ps p₂∈ps n1 (_ ∎) s₁ s₂ x₄ n₂ _ = {!!} -- see TODO
```
#### Deliver
```agda
    knowledge-propagation {N₁} {N₂} {p₁} {p₂} {t₁} {t₂}
      p₁∈ps p₂∈ps x (_ ↝⟨ d@(Deliver (honest {p} {lₚ} {.(⟪ extendTree blockTree _ _ ⟫)} {.(BlockMsg _)} x₁ m∈ms (BlockReceived {b} {t}))) ⟩ N′↝⋆N₂) N₁×p₁≡t₁ x₃ n₂ x₆
      with p₁ ℕ.≟ p
```
adds a block/vote/cert to some p's blocktree
```agda
    ... | no ¬e =
      let r = ∈ₖᵥ-lookup⁺ (∈ₖᵥ-insert⁺ ¬e (∈ₖᵥ-lookup⁻ {m = stateMap N₁} N₁×p₁≡t₁))
      in λ {x₇ → knowledge-propagation {p₁ = p₁} p₁∈ps p₂∈ps (↝∘↝⋆ x d) N′↝⋆N₂ r x₃ n₂ x₆ x₇}
```
adds a block/vote/cert to p₁'s blocktree
```agda
    ... | yes p₁≡p with b ∈? allBlocks blockTree t₂
    -- proof: p₂ either already has the block in the local blocktree or
    --        it is in the message buffer with delay 0 (honest create in prev slot)
    ... | yes b∈t₂ =
      let H₀ = knowledge-propagation {p₁ = p₁} {t₁ = extendTree blockTree t₁ b} p₁∈ps p₂∈ps (↝∘↝⋆ x d) N′↝⋆N₂ {!!} x₃ n₂ x₆
          e = proj₂ $ extendable (is-TreeType blockTree) t₁ b
      in ⊆-trans
           (xs⊆x∷xs (allBlocks blockTree t₁) b)
           (⊆-trans e H₀)

    ... | no b∉t₂ = {!!}

    knowledge-propagation {.(⟦ _ , _ , _ , _ , _ ⟧)} {N₂} {p₁} {p₂} {t₁} {t₂}
      p₁∈ps p₂∈ps x (_ ↝⟨ d@(Deliver (honest {p} {.(⟪ _ ⟫)} {.(⟪ addVote blockTree _ _ ⟫)} {.(VoteMsg _)} x₁ m∈ms VoteReceived)) ⟩ N′↝⋆N₂) N₁×p₁≡t₁ x₃ n₂ x₆ x₇ = {!!}
    knowledge-propagation {N₁} {N₂} {p₁} {p₂} {t₁} {t₂}
      p₁∈ps p₂∈ps x (_ ↝⟨ d@(Deliver (honest {p} {lₚ} {lₚ′} {CertMsg m} x₁ m∈ms x₉)) ⟩ N′↝⋆N₂) N₁×p₁≡t₁ x₃ n₂ x₆ x₇ = {!!}

    knowledge-propagation p₁∈ps p₂∈ps x (_ ↝⟨ Deliver (corrupt m∈ms) ⟩ N′↝⋆N₂) x₂ x₃ n₂ x₆ x₇ = {!!} -- potentially adds a block to p₂'s blocktree in the next slot
```
#### CastVote
CastVote is not relevant for allBlocks
```agda
    knowledge-propagation p₁∈ps p₂∈ps x (_ ↝⟨ d@(CastVote _ (honest x₁ x₉ x₁₀ x₁₁ x₁₂)) ⟩ N′↝⋆N₂) x₂ x₃ n₂ x₆ x₇ =
      knowledge-propagation p₁∈ps p₂∈ps (↝∘↝⋆ x d) N′↝⋆N₂ {!!} x₃ n₂ x₆ x₇
```
#### CreateBlock
```agda
    knowledge-propagation p₁∈ps p₂∈ps x (_ ↝⟨ CreateBlock _ (honest x₁ x₉ x₁₀ x₁₁) ⟩ N′↝⋆N₂) x₂ x₃ n₂ x₆ x₇ = {!!}
```
#### NextSlot
```agda
    knowledge-propagation {N₁} {N₂} p₁∈ps p₂∈ps _ (_ ↝⟨ (NextSlot _) ⟩ N′↝⋆N₂) _ _ _ x₆ _ =
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
