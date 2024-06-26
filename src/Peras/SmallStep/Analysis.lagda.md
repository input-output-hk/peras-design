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
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List.Relation.Unary.All.Properties using (¬Any⇒All¬; All¬⇒¬Any)

open import Function using (_$_; case_of_; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym; trans; subst)

open import Relation.Nullary using (yes; no; ¬_; Dec; contradiction; contraposition)
open import Relation.Nullary.Decidable using (⌊_⌋; _⊎-dec_; toWitness)

open import Peras.Block
open import Peras.Chain
open import Peras.Crypto
open import Peras.Params
open import Peras.SmallStep
open import Peras.Numbering

-- open import Data.List.Membership.DecPropositional _≟-Certificate_ using (_∈?_)

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

    open Semantics {T} {blockTree} {S} {adversarialState₀} {txSelection} {parties}
    open TreeType blockTree
    open IsTreeType
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
```
```agda
    Any-cert→⒈ : ∀ {ts : List T} {r}
      → Any (hasCert r) ts
      → σᵢ r ts ≡ ⒈
    Any-cert→⒈ {ts} {r} x with any? (hasCert? r) ts
    ... | yes p = refl
    ... | no q = ⊥-elim (q x)

    Any-vote→？ : ∀ {ts : List T} {r}
      → ¬ Any (hasCert r) ts
      → Any (hasVote r) ts
      → σᵢ r ts ≡ ？
    Any-vote→？ {ts} {r} x y
      with any? (hasCert? r) ts
      with any? (hasVote? r) ts
    ... | yes p | _     = contradiction p x
    ... | no p  | yes q = refl
    ... | no p  | no q  = ⊥-elim (q y)

    No-vote→🄀 : ∀ {ts : List T} {r}
      → ¬ Any (hasCert r) ts
      → ¬ Any (hasVote r) ts
      → σᵢ r ts ≡ 🄀
    No-vote→🄀 {ts} {r} x y
      with any? (hasCert? r) ts
      with any? (hasVote? r) ts
    ... | yes p | _     = contradiction p x
    ... | no p  | yes q = contradiction q y
    ... | no p  | no q  = refl

    ¬⒈→¬Any-cert : ∀ {ts : List T} {r}
      → σᵢ r ts ≢ ⒈
      → ¬ Any (hasCert r) ts
    ¬⒈→¬Any-cert = contraposition Any-cert→⒈

    ⒈≢？ : ⒈ ≢ ？
    ⒈≢？ ()

    ⒈≢🄀 : ⒈ ≢ 🄀
    ⒈≢🄀 ()
{-
    ⒈→Any-vote : ∀ {ts : List T} {r}
      → σᵢ (MkRoundNumber r) ts ≡ ⒈
      → Any (hasVote (MkRoundNumber (suc r))) ts
    ⒈→Any-vote = {!!}
-}

    ？⇒¬Any-cert : ∀ {ts : List T} {r}
      → σᵢ r ts ≡ ？
      → ¬ Any (hasCert r) ts
    ？⇒¬Any-cert {ts} {r} x = ¬⒈→¬Any-cert λ x₁ →
      contradiction (trans (sym x₁) x) ⒈≢？
```
<!--
```agda
    -- contraposition of quorum-cert from blocktree
{-
    cp : ∀ {r} {t}
         → ¬ hasCert (MkRoundNumber r) t
         → ¬ (length (L.filter (λ {v →
                    (getRoundNumber (votingRound v) Data.Nat.≟ r)
         --     ×-dec (blockHash v ≟-BlockHash hash b)
            }) (votes t)) Data.Nat.≥ τ)
    cp {r} {t} = contraposition (is-TreeType .quorum-cert r t)
-}
```
-->
<!--
```agda
{-
    open import Data.List.Extrema.Core
    open import Data.Nat.Properties using (≤-totalOrder)
    open import Data.List.Extrema (≤-totalOrder) using (argmax)

    xxx : ∀ {f} {xs : List Certificate} {x : Certificate}
      → argmax f x xs ∈ xs ⊎ argmax f x xs ≡ x
    xxx = {!!}

    latestCertSeen∈certs' : ∀ {t} → latestCertSeen t ∈ certs t
    latestCertSeen∈certs' {t} with xxx {roundNumber} {certs t} {cert₀}
    ... | inj₁ x = x
    ... | inj₂ y = {!!}
-}
```
-->
```agda
    open import Data.List.Relation.Binary.Subset.Propositional.Properties
    open import Data.List.Relation.Binary.Subset.Propositional {A = Certificate} using (_⊆_)

    postulate
      latestCertSeen∈certs' : ∀ {t} → latestCertSeen t ∈ certs t

    latestCertSeen∈certs : ∀ {t} → latestCertSeen t L.∷ L.[] ⊆ certs t
    latestCertSeen∈certs (here refl) = latestCertSeen∈certs'
```
```agda
    vr-1a⇒hasCert : ∀ {r} {t}
      → VotingRule-1A (MkRoundNumber (suc r)) t
      → hasCert (MkRoundNumber r) t
    vr-1a⇒hasCert {r} {t} refl =
      Any-resp-⊆ latestCertSeen∈certs
        (here {x = latestCertSeen t} {xs = L.[]} refl)

    vr-1⇒hasCert : ∀ {r} {t}
      → VotingRule-1 (MkRoundNumber (suc r)) t
      → hasCert (MkRoundNumber r) t
    vr-1⇒hasCert = vr-1a⇒hasCert ∘ proj₁

    ？⇒¬AnyVotingRule-1 : ∀ {ts : List T} {r}
      → σᵢ (MkRoundNumber r) ts ≡ ？
      → ¬ Any (VotingRule-1 (MkRoundNumber (suc r))) ts
    ？⇒¬AnyVotingRule-1 {ts} {r} x =
      let s₀ = ？⇒¬Any-cert {ts} {MkRoundNumber r} x
          s₁ = ¬Any⇒All¬ ts s₀
          s₂ = All.map (contraposition vr-1⇒hasCert) s₁
      in All¬⇒¬Any s₂

    ？⇒All¬VotingRule-1 : ∀ {ts : List T} {r}
      → σᵢ (MkRoundNumber r) ts ≡ ？
      → All (¬_ ∘ VotingRule-1 (MkRoundNumber (suc r))) ts
    ？⇒All¬VotingRule-1 {ts} = ¬Any⇒All¬ ts ∘ ？⇒¬AnyVotingRule-1
```
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
    open State

    states₀ : AssocList PartyId T
    states₀ = map (λ where (p , _) → (p , tree₀)) parties

    N₀ : State
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
      prevRound : ∀ (N : State)
        → ∃[ M ] (M ↦ N)

{-
      knowledge-prop : ∀ {m} {M N : State}
        → M ↦⋆ N
        → build-σ′ (MkRoundNumber m) (blockTrees' M) ≡ build-σ′ (MkRoundNumber m) (blockTrees' N)
-}

      knowledge-prop : ∀ {m} {M N : State}
        → M ↦ N
        → build-σ′ (MkRoundNumber m) (blockTrees' M) ≡ build-σ′ (MkRoundNumber m) (blockTrees' N)

      prev-rnd : ∀ {M N : State} {m}
        → M ↦ N
        → suc m ≡ v-rnd' N
        → m ≡ v-rnd' M

      …… : {A : Set} → A
```
#### Theorem 2:
The voting string of every execution of the protocol is built according to the HS-rules
```agda
    theorem-2 : ∀ {M N : State} {m}
      → M ↦ N
      → m ≡ v-rnd' M
      → let σₘ = build-σ (MkRoundNumber m) (blockTrees M)
            σₙ = build-σ (MkRoundNumber (suc m)) (blockTrees N)
        in ∃[ c ] (σₘ ⟶ c × σₙ ≡ c ∷ σₘ)
```
Proof by induction over the voting round.
Base case
```agda
    theorem-2 {M} {N} {zero} _ _ = ⒈ , (HS-I , ……) -- TODO: rewrite with genesis cert
```
Induction step
```agda
    theorem-2 {M} {N} {suc m} M↦N m≡rndM
      with (
        let (M' , M'↦M) = prevRound M
        in theorem-2 {M'} {M} {m} M'↦M (prev-rnd M'↦M m≡rndM)
        )

    theorem-2 {M} {N} {suc m} M↦N m≡rndM | (⒈ , σₘ⟶1 , σₙ≡1∷σₘ)
      rewrite σₙ≡1∷σₘ
      rewrite knowledge-prop {suc m} M↦N
      with any? (hasCert? (MkRoundNumber (suc (suc m)))) (blockTrees' N)
      with any? (hasVote? (MkRoundNumber (suc (suc m)))) (blockTrees' N)
    ... | yes p | _     rewrite Any-cert→⒈ p    = ⒈ , (HS-II-1 , cong (⒈ ∷_) σₙ≡1∷σₘ)
    ... | no ¬p | yes q rewrite Any-vote→？ ¬p q = ？ , (HS-II-? , cong (？ ∷_) σₙ≡1∷σₘ)
    ... | no ¬p | no ¬q rewrite No-vote→🄀 ¬p ¬q = …… -- TODO: contradiction

    theorem-2 {M} {N} {suc m} M↦N m≡rndM | (？ , σₘ⟶? , σₙ≡?∷σₘ)
      rewrite σₙ≡?∷σₘ
      rewrite knowledge-prop {suc m} M↦N
      = 🄀 , HS-III , …… -- TODO

    theorem-2 {M} {N} {suc m} M↦N m≡rndM | (🄀 , σₘ⟶0 , σₙ≡0∷σₘ) = …… -- TODO
```
<!--
```agda
{-
      postulate
        P : ∀ {M N : State} → (M ↝ N) → Set
        Q : ∀ {M N : State} → (M ↝ N) → Set

        theorem-4 : ∀ {M N : State} {m : ℕ}
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
