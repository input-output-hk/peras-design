```agda
module Peras.SmallStep.Analysis where
```
<!--
```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)

open import Peras.Params
```
-->
## Protocol Analysis

### Voting strings

```agda
data Σ : Set where
  ⒈ : Σ
  ？ : Σ
  🄀 : Σ
```
```agda
module _ ⦃ _ : Params ⦄ where
  open import Data.Vec renaming (_∷ʳ_ to _,_)
  open import Data.Nat
  open import Data.Product using (_×_)

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
  VotingString = Vec Σ
  
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
```

```agda
  infix  2 _⟶⋆_
  infixr 2 _⟶⟨_⟩_
  infix  3 _∎

  data _⟶⋆_ : ∀ {m n} → VotingString m → VotingString n → Set where

    _∎ : ∀ {m : ℕ}
      → (M : VotingString m)
        --------------------
      → M ⟶⋆ M

    _⟶⟨_⟩_ : ∀ {l n}
      → (L : VotingString l)
      → {M : VotingString (suc l)} {N : VotingString n}
      → L ⟶ M
      → M ⟶⋆ N
        ------
      → L ⟶⋆ N
```
### Leader strings
```agda
  LeaderString = Vec (ℕ × ℕ)
```
### Execution
```agda
  rnd : ℕ → ⦃ _ : NonZero T ⦄ → ℕ
  rnd s = s / T
```
```agda
  Execution : (m : ℕ) → (n : ℕ) → n ≡ rnd m → Set
  Execution m n refl = LeaderString m × VotingString n
```
## Theorem: The voting string in any execution is valid

<!--
```agda
{-
module Rec where
  open import Data.Vec.Recursive
  open import Data.Product using (_×_; _,_)

  data _⟶_ : ∀ {n} → Σ ^ n → Σ ^ (suc n) → Set where

    HS-I : [] ⟶ ⒈

    HS-II-? : ∀ {σ}
      → (σ , ⒈) ⟶ (σ , ⒈ , ？)

    HS-II-1 : ∀ {σ}
      → (σ , ⒈) ⟶ (σ , ⒈ , ⒈)

    HS-III : ∀ {σ}
      → (σ , ？) ⟶ (σ , ？ , 🄀)

    HS-IV : ∀ {σ n}
      → (σ , ⒈ , ？ , let xx = replicate n 🄀 in {!!}) ⟶ (σ , ⒈ , ？ , 🄀 , 🄀)

  HS-IV : Valid ⟨⟩

  HS-V : Valid ⟨⟩
  HS-VI : Valid ⟨⟩
  HS-VII : Valid ⟨⟩
-}
```
-->
