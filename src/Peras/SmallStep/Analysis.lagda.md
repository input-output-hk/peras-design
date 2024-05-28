```agda
module Peras.SmallStep.Analysis where
```
<!--
```agda
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)

open import Data.Maybe using (just; nothing; Is-just; is-just)
open import Data.Maybe.Properties using (≡-dec)
open import Data.Nat using (ℕ; _+_; _*_; _<ᵇ_; _≤_; _>_; _≥?_; _>?_; zero; suc; NonZero; _/_)

open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Vec as V using (Vec; _∷ʳ_; []; _++_; replicate)
open import Data.List as L using (List; any; map; length; foldr)

open import Data.List.Membership.Propositional as P using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (any?; Any; here; there)

open import Function using (_$_; case_of_; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)

open import Relation.Nullary using (yes; no; ¬_; Dec)
open import Relation.Nullary.Decidable using (⌊_⌋; _⊎-dec_; toWitness)

open import Peras.Block
open import Peras.Chain
open import Peras.Crypto
open import Peras.Params
open import Peras.SmallStep
open import Peras.Numbering

open import Data.Tree.AVL.Map PartyIdO using (Map; lookup; insert; empty; toList)
```
-->
## Protocol Analysis
### Leader strings
```agda
LeaderString = Vec (ℕ × ℕ)
```
### Voting strings
```agda
data Σ : Set where
  ⒈ : Σ
  ？ : Σ
  🄀 : Σ
```
```agda
VotingString = Vec Σ
```
#### Semantics
```agda
module _ {block₀ : Block} {cert₀ : Certificate}
         ⦃ _ : Hashable Block ⦄
         ⦃ _ : Hashable (List Tx) ⦄
         ⦃ _ : Params ⦄
         ⦃ _ : Postulates ⦄

         where

  open Params ⦃...⦄
  open Postulates ⦃...⦄
  open Hashable ⦃...⦄

  module _ {T : Set} (blockTree : TreeType {block₀} {cert₀} T)
           where

    open TreeType blockTree
```
Assign a letter for a voting round for a list of block-trees:

  * 1 : if at least one party saw a round-i block certificate before the end of round i
  * ? : else if at least one party voted in round i
  * 0 : otherwise

```agda
    σᵢ : RoundNumber → List T → Σ
    σᵢ i ts
      with any? (hasCert? i) ts
      with any? (hasVote? i) ts
    ... | yes _ | _     = ⒈
    ... | no _  | yes _ = ？
    ... | no _  | no _  = 🄀
```
Building up the voting string from all the parties block-trees
```agda
    build-σ′ : ∀ (n : ℕ) → List T → Vec Σ n
    build-σ′ 0 _ = []
    build-σ′ (suc n) ts = build-σ′ n ts ∷ʳ σᵢ (MkRoundNumber n) ts

    build-σ : ∀ (n : ℕ) → Map T → Vec Σ n
    build-σ n s = build-σ′ n (map proj₂ (toList s))
```
### Voting string analysis
```agda
    variable
      m n o : ℕ
      ω : LeaderString m
      σ : VotingString n
      σ′ : VotingString (suc n)
      σ″ : VotingString o

    infix 3 _⟶_

    data _⟶_ : VotingString n → Σ → Set where

      HS-I    : [] ⟶ ⒈
      HS-II-? : σ ∷ʳ ⒈ ⟶ ？
      HS-II-1 : σ ∷ʳ ⒈ ⟶ ⒈
      HS-III  : σ ∷ʳ ？ ⟶ 🄀

      HS-IV : ∀ {n} {σ : VotingString n}
        → 1 ≤ L
        → L ≤ K
        → ((σ ∷ʳ ⒈ ∷ʳ ？) ++ replicate L 🄀) ⟶ 🄀

      HS-V-?₁ : ∀ {n} {σ : VotingString n}
        → L + 1 ≡ K
        → ((σ ∷ʳ ⒈ ∷ʳ ？) ++ replicate L 🄀) ⟶ ？

      HS-V-?₂ : ∀ {n} {σ : VotingString n}
        → L + 2 ≡ K
        → ((σ ∷ʳ ⒈ ∷ʳ ？) ++ replicate L 🄀) ⟶ ？

      HS-V-1₁ : ∀ {n} {σ : VotingString n}
        → L + 1 ≡ K
        → ((σ ∷ʳ ⒈ ∷ʳ ？) ++ replicate L 🄀) ⟶ ⒈

      HS-V-1₂ : ∀ {n} {σ : VotingString n}
        → L + 2 ≡ K
        → ((σ ∷ʳ ⒈ ∷ʳ ？) ++ replicate L 🄀) ⟶ ⒈

      HS-VI : ∀ {n} {σ : VotingString n}
        → 1 ≤ L
        → L ≤ K
        → ((σ ∷ʳ 🄀 ∷ʳ ？) ++ replicate L 🄀) ⟶ 🄀

      HS-VII-? : ∀ {n} {σ : VotingString n}
        → L + 1 ≡ K
        → ((σ ∷ʳ 🄀 ∷ʳ ？) ++ replicate L 🄀) ⟶ ？

      HS-VII-1 : ∀ {n} {σ : VotingString n}
        → L + 1 ≡ K
        → ((σ ∷ʳ 🄀 ∷ʳ ？) ++ replicate L 🄀) ⟶ ⒈
```
```agda
    data IsValid : ∀ {n} → VotingString n → Set where

      Empty : IsValid []

      Append : ∀ {m} {v} {σ : VotingString m}
        → IsValid σ
        → (σ ⟶ v)
        → IsValid (σ ∷ʳ v)
```
### Theorem: The voting string in any execution is valid
```agda
    module _ {parties : Parties}
             {S : Set} (adversarialState₀ : S)
             (txSelection : SlotNumber → PartyId → List Tx)
             where

      open State
      open IsTreeType

      GlobalState = State {block₀} {cert₀} {T} {blockTree} {S} {adversarialState₀} {txSelection} {parties}

      states₀ : Map T
      states₀ = foldr (λ where (p , _) m → insert p tree₀ m) empty parties

      N₀ : GlobalState
      N₀ = ⟦ MkSlotNumber 0
           , states₀
           , L.[]
           , L.[]
           , adversarialState₀
           ⟧

      postulate
        genesis-cert′ : ∀ {t} → Any ((0 ≡_) ∘ getRoundNumber ∘ round) (certs t)
        genesis-cert : ∀ {ts} → Any (λ t → Any ((0 ≡_) ∘ getRoundNumber ∘ round) (certs t)) ts

      startsWith-1 : ∀ {ts} → σᵢ (MkRoundNumber 0) ts ≡ ⒈
      startsWith-1 {ts}
        with any? (hasCert? (MkRoundNumber 0)) ts
      ... | yes _ = refl
      ... | no p  = ⊥-elim (p genesis-cert)

{-
      theorem-2′ : ∀ {N : GlobalState} {n : ℕ}
        → N₀ ↝⋆ N
        → IsValid (build-σ (suc n) (stateMap N))
      theorem-2′ {N} {zero} s rewrite startsWith-1 {L.map proj₂ (toList (stateMap N))} = {!!} -- [] ∷ HS-I
      theorem-2′ {N} {suc n} s
        with theorem-2′ {N} {n} s
      ... | xs = {!!}
-}

      postulate
        theorem-2 : ∀ {M N : GlobalState} {m n : ℕ}
          → M ↝⋆ N
          → IsValid (build-σ m (stateMap M))
          → IsValid (build-σ n (stateMap N))
```
## Execution
```agda
    Execution : (m : ℕ) → (n : ℕ) → n ≡ rnd m → Set
    Execution m n refl = LeaderString m × VotingString n
```
## Blocktree with certificates
```agda
    data Edge : Block → Block → Set where

      Parent : ∀ {b b′}
        → parentBlock b′ ≡ hash b
        → Edge b b′

    V = List Block
    E : V → Set
    E vs = List (∀ {v v′ : Block} → {v ∈ vs} → {v′ ∈ vs} → Edge v v′)

    F = ∃[ vs ] (E vs)

    postulate
      IsHonest : Block → Set

    data _⊢_ : ∀ {m n : ℕ} → F → (LeaderString m × VotingString n) → Set where

    record IsPerasBlocktree
      {v : V} {e : E v}
      (root : V → Block)
      (blocktree : (v , e) ⊢ (ω , σ)) : Set where
      -- TODO: A1 - A9
      field
        A1 : IsHonest (root v)

    record PerasBlocktree
      {f : F}
      (blocktree : f ⊢ (ω , σ)): Set where
      field
        root : V → Block
        l# : V → ℕ

        is-PerasBlocktree : IsPerasBlocktree root blocktree
```
