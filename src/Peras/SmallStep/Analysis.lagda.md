```agda
module Peras.SmallStep.Analysis where
```
<!--
```agda
open import Data.Bool as B using (if_then_else_; Bool; true; false)
open import Data.Maybe
open import Data.Maybe.Properties using (≡-dec)
open import Data.Nat
open import Data.Product as P using (_×_)
open import Data.Vec
open import Data.List as L using (List)
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
```agda
module _ {block₀ : Block} {cert₀ : Certificate}
         ⦃ _ : Hashable Block ⦄
         ⦃ _ : Hashable (L.List Tx) ⦄
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
```agda
    isQuorum : RoundNumber → T → Bool
    isQuorum r t =
      let b = tipBest (MkSlotNumber $ getRoundNumber r * U) t
      in quorum t r b
```
```agda
    hasVotes : RoundNumber → T → Bool
    hasVotes r t =
      let b = tipBest (MkSlotNumber $ getRoundNumber r * U) t
      in ⌊ L.length (votes′ t r b) >? 0 ⌋
```
```agda
    σᵢ : ∀ (i : RoundNumber) → L.List T → Σ
    σᵢ i ts
      with any? (B._≟ true) (L.map (isQuorum i) ts)
      with any? (B._≟ true) (L.map (hasVotes i) ts)
    ... | yes p | _     = ⒈
    ... | no _  | yes p = ？
    ... | no _  | no _  = 🄀
```
<!--
```agda
    instance
      nZ : NonZero U -- TODO: why is this needed..?
      nZ = T-nonZero
```
-->
```agda
    variable
      m n o : ℕ
      ω : LeaderString m
      σ : VotingString n
      σ′ : VotingString (suc n)
      σ″ : VotingString o

    module _ where
      open import Data.Vec renaming (_∷ʳ_ to _,_)

      infix 3 _⟶_

      data _⟶_ : VotingString n → VotingString (suc n) → Set where

        HS-I    : [] ⟶ [] , ⒈
        HS-II-? : σ , ⒈ ⟶ σ , ⒈ , ？
        HS-II-1 : σ , ⒈ ⟶ σ , ⒈ , ⒈
        HS-III  : σ , ？ ⟶ σ , ？ , 🄀

        HS-IV : ∀ {n} {σ : VotingString n}
          → 1 ≤ L
          → L ≤ K
          → ((σ , ⒈ , ？) ++ replicate L 🄀) ⟶
            ((σ , ⒈ , ？) ++ replicate L 🄀) , 🄀

        HS-V-?₁ : ∀ {n} {σ : VotingString n}
          → L + 1 ≡ K
          → ((σ , ⒈ , ？) ++ replicate L 🄀) ⟶
            ((σ , ⒈ , ？) ++ replicate L 🄀) , ？

        HS-V-?₂ : ∀ {n} {σ : VotingString n}
          → L + 2 ≡ K
          → ((σ , ⒈ , ？) ++ replicate L 🄀) ⟶
            ((σ , ⒈ , ？) ++ replicate L 🄀) , ？

        HS-V-1₁ : ∀ {n} {σ : VotingString n}
          → L + 1 ≡ K
          → ((σ , ⒈ , ？) ++ replicate L 🄀) ⟶
            ((σ , ⒈ , ？) ++ replicate L 🄀) , ⒈

        HS-V-1₂ : ∀ {n} {σ : VotingString n}
          → L + 2 ≡ K
          → ((σ , ⒈ , ？) ++ replicate L 🄀) ⟶
            ((σ , ⒈ , ？) ++ replicate L 🄀) , ⒈

        HS-VI : ∀ {n} {σ : VotingString n}
          → 1 ≤ L
          → L ≤ K
          → ((σ , 🄀 , ？) ++ replicate L 🄀) ⟶
            ((σ , 🄀 , ？) ++ replicate L 🄀) , 🄀

        HS-VII-? : ∀ {n} {σ : VotingString n}
          → L + 1 ≡ K
          → ((σ , 🄀 , ？) ++ replicate L 🄀) ⟶
            ((σ , 🄀 , ？) ++ replicate L 🄀) , ？

        HS-VII-1 : ∀ {n} {σ : VotingString n}
          → L + 1 ≡ K
          → ((σ , 🄀 , ？) ++ replicate L 🄀) ⟶
            ((σ , 🄀 , ？) ++ replicate L 🄀) , ⒈
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
## Execution
```agda
    rnd : ℕ → ⦃ _ : NonZero U ⦄ → ℕ
    rnd s = s / U
```
```agda
    Execution : (m : ℕ) → (n : ℕ) → n ≡ rnd m → Set
    Execution m n refl = LeaderString m × VotingString n
```
## Theorem: The voting string in any execution is valid


## Blocktree with certificates
```agda
    open import Data.Product using (_,_; ∃-syntax)

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
