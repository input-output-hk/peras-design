```agda
module Peras.SmallStep.Analysis where
```
<!--
```agda
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)

open import Data.Maybe using (just; nothing; Is-just; is-just)
open import Data.Maybe.Properties using (≡-dec)
open import Data.Nat using (ℕ; _+_; _∸_; _*_; _<ᵇ_; _≤_; _>_; _≥?_; _>?_; zero; suc; pred; NonZero; _/_; _≟_)
open import Data.Nat.Properties using (suc-injective)

open import Data.Product using (_,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Data.Vec as V using (Vec; _∷_; []; _++_; replicate)
open import Data.List as L using (List; any; map; length; foldr)

open import Data.List.Membership.Propositional as P using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (any?; Any; here; there)
open import Data.List.Relation.Unary.All using (All)

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

open import Prelude.AssocList
open import Prelude.DecEq using (DecEq)
open import Prelude.Default using (Default)
open Default ⦃...⦄
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
module _ ⦃ _ : Hashable Block ⦄
         ⦃ _ : Hashable (List Tx) ⦄
         ⦃ _ : Params ⦄
         ⦃ _ : Network ⦄
         ⦃ _ : Postulates ⦄

         where

  open Params ⦃...⦄
  open Network ⦃...⦄
  open Postulates ⦃...⦄
  open Hashable ⦃...⦄

  module _ {T : Set} (blockTree : TreeType T)
           {S : Set} (adversarialState₀ : S)
           (txSelection : SlotNumber → PartyId → List Tx)
           (parties : Parties)

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
    build-σ′ : ∀ (n : RoundNumber) → List T → Vec Σ (getRoundNumber n)
    build-σ′ (MkRoundNumber 0) _ = []
    build-σ′ (MkRoundNumber (suc n)) ts =
      σᵢ (MkRoundNumber (suc n)) ts ∷ build-σ′ (MkRoundNumber n) ts

    build-σ : ∀ (n : RoundNumber) → AssocList PartyId T → Vec Σ (getRoundNumber n)
    build-σ n = build-σ′ n ∘ map proj₂
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
      HS-II-? : ⒈ ∷ σ ⟶ ？
      HS-II-1 : ⒈ ∷ σ ⟶ ⒈
      HS-III  : ？ ∷ σ ⟶ 🄀

      HS-IV : ∀ {n} {σ : VotingString n}
        → 1 ≤ L
        → L ≤ K
        → (replicate L 🄀 ++ (？ ∷ ⒈ ∷ σ)) ⟶ 🄀
{-
      HS-V-?₁ : ∀ {n} {σ : VotingString n}
        → L + 1 ≡ K
        → (replicate L 🄀 ++ (？ ∷ ⒈ ∷ σ)) ⟶ ？

      HS-V-?₂ : ∀ {n} {σ : VotingString n}
        → L + 2 ≡ K
        → (replicate L 🄀 ++ (？ ∷ ⒈ ∷ σ)) ⟶ ？

      HS-V-1₁ : ∀ {n} {σ : VotingString n}
        → L + 1 ≡ K
        → (replicate L 🄀 ++ (？ ∷ ⒈ ∷ σ)) ⟶ ⒈

      HS-V-1₂ : ∀ {n} {σ : VotingString n}
        → L + 2 ≡ K
        → (replicate L 🄀 ++ (？ ∷ ⒈ ∷ σ)) ⟶ ⒈

      HS-VI : ∀ {n} {σ : VotingString n}
        → 1 ≤ L
        → L ≤ K
        → (replicate L 🄀 ++ (？ ∷ 🄀 ∷ σ)) ⟶ 🄀

      HS-VII-? : ∀ {n} {σ : VotingString n}
        → L + 1 ≡ K
        → (replicate L 🄀 ++ (？ ∷ 🄀 ∷ σ)) ⟶ ？

      HS-VII-1 : ∀ {n} {σ : VotingString n}
        → L + 1 ≡ K
        → (replicate L 🄀 ++ (？ ∷ 🄀 ∷ σ)) ⟶ ⒈
-}
```
```agda
    postulate
      lastIsHead : ∀ {ts : List T} {m} {x}
        → build-σ′ (MkRoundNumber m) ts ⟶ x
        → V.head (build-σ′ (MkRoundNumber (suc m)) ts) ≡ x

    ？→¬VotingRule-1 : ∀ {ts : List T} {r}
      → build-σ′ (MkRoundNumber r) ts ⟶ ？
      → All (λ {t → ¬ VotingRule-1 {T} {blockTree} {S} {adversarialState₀} {txSelection} {parties} (MkRoundNumber (suc r)) t}) ts
    ？→¬VotingRule-1 {ts} {zero} ()
    ？→¬VotingRule-1 {ts} {suc r} x = {!!}
```
<!--
```agda
{-
    lastIsHead {ts} {m} {x} x₁
      with (build-σ′ (MkRoundNumber (suc m)) ts)
    ... | (x₂ ∷ _)
      with any? (hasCert? (MkRoundNumber (suc m))) ts
      with any? (hasVote? (MkRoundNumber (suc m))) ts
    lastIsHead {ts} {m} {⒈} x₁ | x₂ ∷ _ | yes _ | _    = refl
    lastIsHead {ts} {m} {⒈} x₁ | x₂ ∷ _ | no _ | yes _ = {!!}
    lastIsHead {ts} {m} {⒈} x₁ | x₂ ∷ _ | no _ | no _  = {!!}
    lastIsHead {ts} {m} {？} x₁ | x₂ ∷ _ | no  _ | yes _ = refl
    lastIsHead {ts} {m} {🄀} x₁ | x₂ ∷ _ | no _  | no _  = refl
-}
```
-->
<!--
Reflexive, transitive closure
```agda
{-
    infix 2 _⟶⋆_

    data _⟶⋆_ : VotingString m → VotingString n → Set where
      [] : σ ⟶⋆ σ
      _<>_ : ∀ {i} → σ ⟶⋆ σ″ → (σ″ ⟶ i) → σ ⟶⋆ (i ∷ σ″)
-}
```
-->
<!--
```
{-
    data IsValid : ∀ {n} → VotingString n → Set where

      ϵ : IsValid []

      _∷_ : ∀ {m} {v} {σ : VotingString m}
        → IsValid σ
        → (σ ⟶ v)
        → IsValid (σ ∷ʳ v)
-}
```
-->
### Theorem: The voting string in any execution is valid
```agda
    module _ {parties : Parties}
             {S : Set} (adversarialState₀ : S)
             (txSelection : SlotNumber → PartyId → List Tx)
             where

      open State
      open IsTreeType

      GlobalState = State {T} {blockTree} {S} {adversarialState₀} {txSelection} {parties}

      states₀ : AssocList PartyId T
      states₀ = map (λ where (p , _) → (p , tree₀)) parties

      N₀ : GlobalState
      N₀ = ⟦ MkSlotNumber 0
           , states₀
           , L.[]
           , L.[]
           , adversarialState₀
           ⟧
```
<!--
```agda
{-
      postulate
        genesis-cert′ : ∀ t → hasCert (MkRoundNumber 1) t
        genesis-cert : ∀ ts → All (hasCert (MkRoundNumber 0)) ts

      HS-I-rule : ∀ {ts} → σᵢ (MkRoundNumber 0) ts ≡ ⒈
      HS-I-rule {ts}
        with any? (hasCert? (MkRoundNumber 0)) ts
      ... | yes _ = refl
      ... | no p  = ⊥-elim (p genesis-cert)
-}
```
```agda
{-
      postulate
        theorem-2 : ∀ {M N : GlobalState} {m n : ℕ}
          → M ↝⋆ N
          → build-σ m (blockTrees M) ⟶⋆ build-σ n (blockTrees N)
-}
{-
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
-}
```
-->
```agda
      postulate
        prevRound : ∀ (N : GlobalState)
          → ∃[ M ] (M ↦ N)

        knowledge-prop : ∀ {m} {M N : GlobalState}
          → M ↦⋆ N
          → build-σ′ (MkRoundNumber m) (blockTrees' M) ≡ build-σ′ (MkRoundNumber m) (blockTrees' N)

        prev-rnd : ∀ {M N : GlobalState} {m}
          → M ↦ N
          → suc m ≡ v-rnd' N
          → m ≡ v-rnd' M

        …… : {A : Set} → A
```
#### Theorem 2:
The voting string of every execution of the protocol is built according to the HS-rules
```agda
      -- preconditions
      -- * transition to new voting round
      -- * required votes from the previous round
      theorem-2 : ∀ {M N : GlobalState} {m}
        → M ↦ N
        → m ≡ v-rnd' M
        → let σₘ = build-σ (MkRoundNumber m) (blockTrees M)
              σₙ = build-σ (MkRoundNumber (suc m)) (blockTrees N)
          in ∃[ c ] (σₘ ⟶ c × σₙ ≡ c ∷ σₘ)
      theorem-2 {M} {N} {zero} _ _ = ⒈ , (HS-I , ……) -- TODO: rewrite with genesis cert
      theorem-2 {M} {N} {suc m} M↦N m≡rndM
        with
          (let (M' , M'↦M) = prevRound M
           in theorem-2 {M'} {M} {m} M'↦M (prev-rnd M'↦M m≡rndM))
      theorem-2 {M} {N} {suc m} M↦N m≡rndM | (c , st″ , σ′)
        rewrite σ′
        rewrite knowledge-prop {m} (proj₂ (prevRound M) ⨾ M↦N ⨾ ρ)
        rewrite lastIsHead {blockTrees' N} st″
        with c

      theorem-2 {M} {N} {suc m} M↦N _ | (c , st″ , σ′) | ⒈
        with any? (hasCert? (MkRoundNumber (suc (suc m)))) (blockTrees' N)
        with any? (hasVote? (MkRoundNumber (suc (suc m)))) (blockTrees' N)
      ... | yes _ | _     = ⒈ , (HS-II-1 , refl)
      ... | no _  | yes _ = ？ , (HS-II-? , refl)
      ... | no _  | no _  = …… -- TODO: contradiction

      theorem-2 {M} {N} {suc m} M↦N m≡rndM | (c , st″ , σ′) | ？ = 🄀 , HS-III , …… -- TODO
      theorem-2 {M} {N} {suc m} M↦N m≡rndM | (c , st″ , σ′) | 🄀 = …… -- TODO
```
<!--
```agda
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
-->
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
