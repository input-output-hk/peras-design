```agda
module Peras.SmallStep.Analysis where
```
<!--
```agda
open import Data.Bool using (Bool; true; false)
open import Data.Maybe.Properties using (≡-dec)
open import Data.Nat using (ℕ; _+_; _*_; _<ᵇ_; _≤_; zero; suc; NonZero; _/_)

open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Vec using (Vec; _∷ʳ_; []; _++_; replicate)
open import Data.List using (List; any; map; length)
open import Data.List.Membership.Propositional as P using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (any?; Any; here; there)

open import Function using (_$_; case_of_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)

open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Peras.Block
open import Peras.Chain
open import Peras.Crypto
open import Peras.Params
open import Peras.SmallStep
open import Peras.Numbering

open import Data.Tree.AVL.Map PartyIdO using (Map; lookup; insert; empty)
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
The function indicates whether there has been a quorum of votes in a voting
round for a given block-tree.
```agda
    hasQuorum : RoundNumber → T → Bool
    hasQuorum r t =
      let b = tipBest (MkSlotNumber $ getRoundNumber r * U) t
      in quorum t r b
```
The function indicates whether there a vote has been seen in a voting round
for a given block-tree.
```agda
    hasVotes : RoundNumber → T → Bool
    hasVotes r t =
      let b = tipBest (MkSlotNumber $ getRoundNumber r * U) t
      in 0 <ᵇ length (votes′ t r b)
```
Assign a letter for a voting round for a given block-tree
```agda
    σᵢ : ∀ (i : RoundNumber) → List T → Σ
    σᵢ i ts
      with any (hasQuorum i) ts
      with any (hasVotes i) ts
    ... | true  | _     = ⒈
    ... | false | true  = ？
    ... | false | false = 🄀
```
```agda
    postulate
      build-σ : ∀ {n} → Map T → VotingString n
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

    data _⟶_ : VotingString n → VotingString (suc n) → Set where

      HS-I    : [] ⟶ [] ∷ʳ ⒈
      HS-II-? : σ ∷ʳ ⒈ ⟶ σ ∷ʳ ⒈ ∷ʳ ？
      HS-II-1 : σ ∷ʳ ⒈ ⟶ σ ∷ʳ ⒈ ∷ʳ ⒈
      HS-III  : σ ∷ʳ ？ ⟶ σ ∷ʳ ？ ∷ʳ 🄀

      HS-IV : ∀ {n} {σ : VotingString n}
        → 1 ≤ L
        → L ≤ K
        → ((σ ∷ʳ ⒈ ∷ʳ ？) ++ replicate L 🄀) ⟶
          ((σ ∷ʳ ⒈ ∷ʳ ？) ++ replicate L 🄀) ∷ʳ 🄀

      HS-V-?₁ : ∀ {n} {σ : VotingString n}
        → L + 1 ≡ K
        → ((σ ∷ʳ ⒈ ∷ʳ ？) ++ replicate L 🄀) ⟶
          ((σ ∷ʳ ⒈ ∷ʳ ？) ++ replicate L 🄀) ∷ʳ ？

      HS-V-?₂ : ∀ {n} {σ : VotingString n}
        → L + 2 ≡ K
        → ((σ ∷ʳ ⒈ ∷ʳ ？) ++ replicate L 🄀) ⟶
          ((σ ∷ʳ ⒈ ∷ʳ ？) ++ replicate L 🄀) ∷ʳ ？

      HS-V-1₁ : ∀ {n} {σ : VotingString n}
        → L + 1 ≡ K
        → ((σ ∷ʳ ⒈ ∷ʳ ？) ++ replicate L 🄀) ⟶
          ((σ ∷ʳ ⒈ ∷ʳ ？) ++ replicate L 🄀) ∷ʳ ⒈

      HS-V-1₂ : ∀ {n} {σ : VotingString n}
        → L + 2 ≡ K
        → ((σ ∷ʳ ⒈ ∷ʳ ？) ++ replicate L 🄀) ⟶
          ((σ ∷ʳ ⒈ ∷ʳ ？) ++ replicate L 🄀) ∷ʳ ⒈

      HS-VI : ∀ {n} {σ : VotingString n}
        → 1 ≤ L
        → L ≤ K
        → ((σ ∷ʳ 🄀 ∷ʳ ？) ++ replicate L 🄀) ⟶
          ((σ ∷ʳ 🄀 ∷ʳ ？) ++ replicate L 🄀) ∷ʳ 🄀

      HS-VII-? : ∀ {n} {σ : VotingString n}
        → L + 1 ≡ K
        → ((σ ∷ʳ 🄀 ∷ʳ ？) ++ replicate L 🄀) ⟶
          ((σ ∷ʳ 🄀 ∷ʳ ？) ++ replicate L 🄀) ∷ʳ ？

      HS-VII-1 : ∀ {n} {σ : VotingString n}
        → L + 1 ≡ K
        → ((σ ∷ʳ 🄀 ∷ʳ ？) ++ replicate L 🄀) ⟶
          ((σ ∷ʳ 🄀 ∷ʳ ？) ++ replicate L 🄀) ∷ʳ ⒈
```
Reflexive, transitive closure of the small step relation
```agda
    infix  2 _⟶⋆_
```
```agda
    data _⟶⋆_ : VotingString m → VotingString n → Set where
      [] : σ ⟶⋆ σ
      _∷_ : σ ⟶ σ′ → σ′ ⟶⋆ σ″ → σ ⟶⋆ σ″
```
### Theorem: The voting string in any execution is valid
```agda
    module _ {parties : Parties}
             {S : Set} (adversarialState₀ : S)
             (txSelection : SlotNumber → PartyId → List Tx)
             where

      open State

      GlobalState = State {block₀} {cert₀} {T} {blockTree} {S} {adversarialState₀} {txSelection} {parties}

      postulate
        theorem-2 : ∀ {M N : GlobalState}
          → M ↝⋆ N
          → build-σ {m} (stateMap M) ⟶⋆ build-σ {n} (stateMap N)

```
## Execution
```agda
    rnd : ℕ → ⦃ _ : NonZero U ⦄ → ℕ
    rnd s = s / U
```
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
