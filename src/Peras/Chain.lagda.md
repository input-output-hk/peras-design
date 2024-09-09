```agda
module Peras.Chain where
```

<!--
```agda
open import Data.Bool using (_∧_; true; false)
open import Data.List using (sum; upTo; applyUpTo; filterᵇ; filter; concat; mapMaybe; zip) renaming (length to ∣_∣)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (any?; Any; here; there; lookup)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe as M using (nothing; just)
open import Data.Nat using (ℕ; _/_; _>_; _≥_; _≥?_; _≤?_; NonZero; pred; _∸_; z≤n; s≤s)
open import Data.Nat using (_≤_; _<_; _∸_)
open import Data.Nat.Properties using (n≮n; _≟_)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
open import Function.Base using (_∘_; _$_)
open import Relation.Nullary using (¬_; Dec; yes; no; ¬?)
open import Relation.Nullary.Decidable using (_×-dec_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Peras.Crypto
open import Peras.Block
open import Peras.Numbering
open import Peras.Params

open import Haskell.Prelude hiding (length; _<_; _>_; _∘_; sum; b; pred; filter; concat; _$_; lookup; zip; All; Any; _,_; _×_)
open import Haskell.Law.Equality using (cong)

{-# FOREIGN AGDA2HS
{-# LANGUAGE DeriveGeneric #-}
import GHC.Generics (Generic)
#-}

{-# FOREIGN GHC
import qualified Peras.Chain as G
#-}
```
-->

## Voting

### Vote

```agda
VotingWeight = ℕ

record Vote : Set where
  constructor MkVote
  field votingRound : RoundNumber
        creatorId   : PartyId
        proofM      : MembershipProof
        blockHash   : Hash Block
        signature   : Signature

  votingRound' : ℕ
  votingRound' = getRoundNumber votingRound

open Vote public

instance
  iVoteEq : Eq Vote
  iVoteEq ._==_ x y = votingRound x == votingRound y
                        && creatorId x == creatorId y
                        && proofM x == proofM y
                        && blockHash x == blockHash y
                        && signature x == signature y
```

<!--
```agda
{-# COMPILE AGDA2HS VotingWeight #-}
{-# COMPILE AGDA2HS Vote deriving (Generic) #-}
{-# COMPILE GHC Vote = data G.Vote (G.MkVote) #-}
{-# COMPILE AGDA2HS iVoteEq #-}
```
-->
```agda
record Postulates : Set₁ where
  field
    IsSlotLeader : PartyId → SlotNumber → LeadershipProof → Set
    IsCommitteeMember : PartyId → RoundNumber → MembershipProof → Set
    IsBlockSignature : Block → Signature → Set
    IsVoteSignature : Vote → Signature → Set

record Network : Set₁ where
  field
    Δ : ℕ
```
```agda
module _ ⦃ _ : Postulates ⦄
         where

  open Postulates ⦃...⦄

  ValidVote : Vote → Set
  ValidVote v =
    IsCommitteeMember
        (creatorId v)
        (votingRound v)
        (proofM v)
    × IsVoteSignature v (signature v)
```

### Equivocation relation

Equivocal votes are multiple votes by the same party for the same round.

```agda
data _∻_ : Vote → Vote → Set where

  Equivocation : ∀ {v₁ v₂}
    → creatorId v₁ ≡ creatorId v₂
    → votingRound v₁ ≡ votingRound v₂
    → v₁ ≢ v₂
    → v₁ ∻ v₂
```
## Chain

```agda
Chain = List Block
```
<!--
```agda
{-# COMPILE AGDA2HS Chain #-}
```
-->

```agda
certsFromChain : Chain → List Certificate
certsFromChain = mapMaybe certificate
```
```agda
insertCert : Certificate → List Certificate → List Certificate
insertCert cert [] = cert ∷ []
insertCert cert (cert' ∷ certs) =
  if cert == cert'
  then cert' ∷ certs
  else cert' ∷ insertCert cert certs

{-# COMPILE AGDA2HS insertCert #-}
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
prune : SlotNumber → Chain → Chain
prune (MkSlotNumber sl) = filter ((_≤? sl) ∘ slotNumber')
```
### Chain weight

The weight of a chain is defined with respect of the Peras parameters
```agda
open Params ⦃...⦄
```

```agda
module _ ⦃ _ : Hashable Block ⦄
         where

  open Hashable ⦃...⦄

  ChainExtends : Hash Block → Certificate → Chain → Set
  ChainExtends h c =
    Any (λ block → (hash block ≡ blockRef c))
      ∘ Data.List.dropWhile (λ block' → ¬? (hash block' ≟-BlockHash h))

  ChainExtends? : (h : Hash Block) → (c : Certificate) → (chain : Chain) → Dec (ChainExtends h c chain)
  ChainExtends? h c =
    any? (λ block → (hash block ≟-BlockHash blockRef c))
      ∘ Data.List.dropWhile (λ block' → ¬? (hash block' ≟-BlockHash h))

  Extends : Hash Block → Certificate → List Chain → Set
  Extends h c = Any (ChainExtends h c)

  Extends? : (h : Hash Block) → (c : Certificate) → (chains : List Chain) → Dec (Extends h c chains)
  Extends? h c = any? (ChainExtends? h c)
```

```agda
  tipHash : Chain → Hash Block
  tipHash [] = record { hashBytes = emptyBS }
  tipHash (b ∷ _) = hash b
```

The weight of a chain is computed wrt to a set of dangling votes
```agda
module _ ⦃ _ : Hashable Block ⦄
         ⦃ _ : Params ⦄
         where
```
```agda
  open Hashable ⦃...⦄
```
```agda
  _PointsInto_ : Certificate → Chain → Set
  _PointsInto_ c = Any ((blockRef c ≡_) ∘ hash)
```
```agda
  _PointsInto?_ : ∀ (c : Certificate) → (ch : Chain) → Dec (c PointsInto ch)
  _PointsInto?_ c = any? ((blockRef c ≟-BlockHash_) ∘ hash)
```
```agda
  StartOfRound : SlotNumber → RoundNumber → Set
  StartOfRound (MkSlotNumber sl) (MkRoundNumber r) = sl ≡ r * U
```
```agda
  StartOfRound? : (sl : SlotNumber) → (r : RoundNumber) → Dec (StartOfRound sl r)
  StartOfRound? (MkSlotNumber sl) (MkRoundNumber r) = sl ≟ r * U
```
```agda
  rnd : ℕ → ⦃ _ : NonZero U ⦄ → ℕ
  rnd s = s / U
```
```agda
  v-round : SlotNumber → RoundNumber
  v-round (MkSlotNumber s) = MkRoundNumber (rnd s)
```
### Chain weight

```agda
  ∥_∥_ : Chain → List Certificate → ℕ
  ∥ ch ∥ cts = ∣ ch ∣ + ∣ filter (_PointsInto? ch) cts ∣ * B
```

### Chain validity

<!--
```agda
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (trans)

open Block
```
-->
```agda
module _ ⦃ _ : Hashable Block ⦄
         ⦃ _ : Postulates ⦄
         ⦃ _ : Network ⦄

         where

  open Hashable ⦃...⦄
  open Postulates ⦃...⦄
  open Network ⦃...⦄
```
```agda
  data ValidChain : Chain → Set where

    Genesis : ValidChain []

    Cons : ∀ {c : Chain} {b : Block}
      → IsBlockSignature b (signature b)
      → IsSlotLeader (creatorId b) (slotNumber b) (leadershipProof b)
      → parentBlock b ≡ tipHash c
      → ValidChain c
      → ValidChain (b ∷ c)
```
<!--
```agda
-- | `foldl` does not exist in `Haskell.Prelude` so let's roll our own
-- but let's make it total.
foldl1Maybe : ∀ {a : Set} -> (a -> a -> a) -> List a -> Maybe a
foldl1Maybe f xs =
  foldl (λ m y -> Just (case m of λ where
                             Nothing -> y
                             (Just x)  -> f x y))
        Nothing xs

{-# COMPILE AGDA2HS foldl1Maybe #-}

prefix : List Block -> List Block -> List Block -> List Block
prefix acc (x ∷ xs) (y ∷ ys) =
  if x == y
   then prefix (x ∷ acc) xs ys
   else reverse acc
prefix acc _ _ = reverse acc

{-# COMPILE AGDA2HS prefix #-}

commonPrefix : List Chain -> List Block
commonPrefix chains =
  case listPrefix of λ where
     Nothing -> []
     (Just bs) -> reverse bs
   where
     listPrefix : Maybe (List Block)
     listPrefix = foldl1Maybe (prefix []) (map (λ l -> reverse l) chains)

{-# COMPILE AGDA2HS commonPrefix #-}
-->
