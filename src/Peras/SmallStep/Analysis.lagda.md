```agda
module Peras.SmallStep.Analysis where
```
<!--
```agda
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)

open import Data.Maybe using (just; nothing; Is-just; is-just)
open import Data.Maybe.Properties using (≡-dec)
open import Data.Nat using (ℕ; _+_; _*_; _<ᵇ_; _≤_; _>_; _≥?_; _>?_; zero; suc; NonZero; _/_; _≟_)

open import Data.Product using (_,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Data.Vec as V using (Vec; _∷ʳ_; []; _++_; replicate)
open import Data.List as L using (List; any; map; length; foldr)

open import Data.List.Membership.Propositional as P using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (any?; Any; here; there)

open import Function using (_$_; case_of_; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym; trans)

open import Relation.Nullary using (yes; no; ¬_; Dec; contradiction)
open import Relation.Nullary.Decidable using (⌊_⌋; _⊎-dec_; toWitness)

open import Peras.Block
open import Peras.Chain
open import Peras.Crypto
open import Peras.Params
open import Peras.SmallStep
open import Peras.Numbering

open import Prelude.AssocList hiding (_∈_)
open Decidable _≟_
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
Building up the voting string from all the party's block-trees
```agda
    build-σ : ∀ (n : ℕ) → AssocList PartyId T → Vec Σ n
    build-σ n = build-σ′ n ∘ map proj₂
      where
        build-σ′ : ∀ (n : ℕ) → List T → Vec Σ n
        build-σ′ 0 _ = []
        build-σ′ (suc n) ts = build-σ′ n ts ∷ʳ σᵢ (MkRoundNumber n) ts
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
    infix 2 _⟶⋆_

    data _⟶⋆_ : VotingString m → VotingString n → Set where
      [] : σ ⟶⋆ σ
      _∷_ : ∀ {i} → σ ⟶⋆ σ″ → (σ″ ⟶ i) → σ ⟶⋆ (σ″ ∷ʳ i)

{-
    data IsValid : ∀ {n} → VotingString n → Set where

      ϵ : IsValid []

      _∷_ : ∀ {m} {v} {σ : VotingString m}
        → IsValid σ
        → (σ ⟶ v)
        → IsValid (σ ∷ʳ v)
-}
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

      states₀ : AssocList PartyId T
      states₀ = map (λ where (p , _) → (p , tree₀)) parties

      N₀ : GlobalState
      N₀ = ⟦ MkSlotNumber 0
           , states₀
           , L.[]
           , L.[]
           , adversarialState₀
           ⟧

      postulate
        genesis-cert′ : ∀ {t} → Any ((0 ≡_) ∘ roundNumber) (certs t)
        genesis-cert : ∀ {ts} → Any (λ t → Any ((0 ≡_) ∘ roundNumber) (certs t)) ts

      HS-I-rule : ∀ {ts} → σᵢ (MkRoundNumber 0) ts ≡ ⒈
      HS-I-rule {ts}
        with any? (hasCert? (MkRoundNumber 0)) ts
      ... | yes _ = refl
      ... | no p  = ⊥-elim (p genesis-cert)

      postulate
        theorem-2 : ∀ {M N : GlobalState} {m n : ℕ}
          → M ↝⋆ N
          → build-σ m (blockTrees M) ⟶⋆ build-σ n (blockTrees N)

      lemma-length-σ′ : ∀ {tₘ tₙ} {m n : ℕ}
          → m ≡ n
          → let σₘ = build-σ m tₘ
                σₙ = build-σ n tₙ
             in V.length σₘ ≡ V.length σₙ
      lemma-length-σ′ refl = refl

      lemma-length-σ : ∀ {M N : GlobalState}
          → v-round (clock M) ≡ v-round (clock N)
          → let σₘ = build-σ (getRoundNumber (v-round (clock M))) (blockTrees M)
                σₙ = build-σ (getRoundNumber (v-round (clock N))) (blockTrees N)
             in V.length σₘ ≡ V.length σₙ
      lemma-length-σ {M} {N} x = lemma-length-σ′ {blockTrees M} {blockTrees N} (cong getRoundNumber x)

      -- preconditions
      -- * transition to new voting round
      -- * required votes from the previous round
      postulate
        theorem-3 : ∀ {M N : GlobalState} {m}
          → M ↝⋆ N
          → rnd (getSlotNumber (clock M)) ≡ m
          → rnd (getSlotNumber (clock N)) ≡ suc m
          → RequiredVotes M
          → RequiredVotes N
          → let σₘ = build-σ m (blockTrees M)
                σₙ = build-σ (suc m) (blockTrees N)
            in ∃[ c ] (σₘ ⟶ c × σₙ ≡ σₘ ∷ʳ c)

{-
      theorem-3 {M} {N} st refl x a b
        with any? (hasCert? (v-round (clock M))) (map proj₂ $ blockTrees M)
        with any? (hasCert? (v-round (clock N))) (map proj₂ $ blockTrees N)
      ... | yes _ | yes _  = (⒈ , ({!HS-II-1!} , {!!}))
      ... | _ | _ = {!!}
-}

{-
      postulate
        P : ∀ {M N : GlobalState} → (M ↝ N) → Set
        Q : ∀ {M N : GlobalState} → (M ↝ N) → Set

        theorem-4 : ∀ {M N : GlobalState} {m : ℕ}
          → (st : M ↝ N)
          → (let σₘ = build-σ m (blockTrees M)
                 σₙ = build-σ m (blockTrees N)
             in P st × (σₘ ≡ σₙ) -- FIXME: σₘ ≡ σₙ does not have to hold
                                 -- that last element in the vector can change
            )
            ⊎
            (let σₘ = build-σ m (blockTrees M)
                 σₙ = build-σ (suc m) (blockTrees N)
             in Q st × ∃[ c ] (σₘ ⟶ c × σₙ ≡ σₘ ∷ʳ c)
            )
-}
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
