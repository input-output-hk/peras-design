```agda
module Peras.SmallStep.Analysis where
```
<!--
```agda
open import Data.Nat
open import Data.Product using (_×_)
open import Data.Vec renaming (_∷ʳ_ to _,_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)

open import Peras.Params
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
module _ ⦃ _ : Params ⦄ where
  open Params ⦃...⦄
```
<!--
```agda
  instance
    nZ : NonZero T -- TODO: why is this needed..?
    nZ = T-nonZero
```
-->
```agda
  infix 3 _⟶_

  data _⟶_ : ∀ {n} → VotingString n → VotingString (suc n) → Set where

    HS-I : [] ⟶ [] , ⒈

    HS-II-? : ∀ {n} {σ : VotingString n}
      → σ , ⒈ ⟶ σ , ⒈ , ？

    HS-II-1 : ∀ {n} {σ : VotingString n}
      → σ , ⒈ ⟶ σ , ⒈ , ⒈

    HS-III : ∀ {n} {σ : VotingString n}
      → σ , ？ ⟶ σ , ？ , 🄀

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
  
  variable
    m n o : ℕ
    ω : LeaderString m
    σ : VotingString n
    σ′ : VotingString (suc n)
    σ″ : VotingString o
```
```agda
  data _⟶⋆_ : VotingString m → VotingString n → Set where
    [] : σ ⟶⋆ σ
    _∷_ : σ ⟶ σ′ → σ′ ⟶⋆ σ″ → σ ⟶⋆ σ″
```
## Execution
```agda
  rnd : ℕ → ⦃ _ : NonZero T ⦄ → ℕ
  rnd s = s / T
```
```agda
  Execution : (m : ℕ) → (n : ℕ) → n ≡ rnd m → Set
  Execution m n refl = LeaderString m × VotingString n
```
## Theorem: The voting string in any execution is valid

TODO

## Blocktree with certificates
```agda
  open import Peras.Block
  open import Peras.Crypto
  open import Data.List using (List)
  open import Data.List.Membership.Propositional as P using (_∈_; _∉_)

  module _ ⦃ _ : Hashable Block ⦄ where

    open Hashable ⦃...⦄

    data Edge : Block → Block → Set where

      Parent : ∀ {b b′}
        → parentBlock b′ ≡ hash b
        → Edge b b′

    V = List Block
    E = (v : V) → List (∀ {b b′ : Block} → {b ∈ v} → {b′ ∈ v} → Edge b b′)

    F = V × E

    data _⊢_ : ∀ {m n : ℕ} → F → (LeaderString m × VotingString n) → Set where

    record IsPerasBlocktree
      {f : F}
      (blocktree : f ⊢ (ω Data.Product., σ)): Set where
      -- TODO: A1 - A9

    record PerasBlocktree
      {f : F}
      (blocktree : f ⊢ (ω Data.Product., σ)): Set where
      field
        is-PerasBlocktree : IsPerasBlocktree blocktree
```
