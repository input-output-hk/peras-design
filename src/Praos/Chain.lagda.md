```agda
module Praos.Chain where
```

<!--
```agda
open import Data.List using (List; _++_; _∷_; []; filter)
open import Data.Nat using (_≤?_)
open import Function.Base using (_∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Relation.Binary using (DecidableEquality)

open import Praos.Block
open import Praos.Crypto
```
-->

## Chain

```agda
Chain = List Block
```

### Chain prefix

```agda
data _⪯_ : Chain → Chain → Set where

  Prefix : ∀ {c₁ c₂ c₃ : Chain}
    → c₁ ++ c₃ ≡ c₂
    → c₁ ⪯ c₂
```

### Chain pruning

```agda
prune : Slot → Chain → Chain
prune sl = filter ((_≤? sl) ∘ slotNumber)
```
```agda
module _ ⦃ _ : Hashable Block ⦄
         where
```

### Chain validity

<!--
```agda
open import Relation.Nullary.Negation using (¬_)

import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (trans)

open Block

open import Data.List.Membership.Propositional using (_∈_)
```
-->
```agda
module _ {block₀ : Block}
         {IsSlotLeader : PartyId → Slot → LeadershipProof → Set}
         {IsBlockSignature : Block → Signature → Set}
         ⦃ _ : Hashable Block ⦄
         where

  open Hashable ⦃...⦄
```
```agda
  data ValidChain : Chain → Set where

    Genesis :
      ValidChain (block₀ ∷ [])

    Cons : ∀ {c : Chain} {b₁ b₂ : Block}
      → IsBlockSignature b₁ (signature b₁)
      → IsSlotLeader (creatorId b₁) (slotNumber b₁) (leadershipProof b₁)
      → parentBlock b₁ ≡ hash b₂
      → ValidChain (b₂ ∷ c)
      → ValidChain (b₁ ∷ (b₂ ∷ c))
```
```agda
  tip : ∀ {c : Chain} → ValidChain c → Block
  tip Genesis = block₀
  tip (Cons {c} {b} _ _ _ _) = b
```
