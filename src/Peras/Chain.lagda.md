```agda
module Peras.Chain where
```
```agda
open import Haskell.Prelude
open import Haskell.Extra.Dec
open import Haskell.Extra.Refinement
open import Haskell.Law.Equality

open import Data.Nat using (NonZero; _/_)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Peras.Crypto
open import Peras.Block
open import Peras.Numbering
open import Peras.Params
open import Peras.Util

{-# FOREIGN AGDA2HS
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -fno-warn-missing-pattern-synonym-signatures #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
import GHC.Generics (Generic)
#-}

{-# FOREIGN GHC
import qualified Peras.Chain as G
#-}
```
## Voting

### Vote

```agda
VotingWeight = Nat

record Vote : Set where
  constructor MkVote
  field votingRound : RoundNumber
        creatorId   : PartyId
        proofM      : MembershipProof
        blockHash   : Hash Block
        signature   : Signature

  votingRound' : Nat
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
```agda
{-# COMPILE AGDA2HS VotingWeight #-}
{-# COMPILE AGDA2HS Vote deriving (Generic) #-}
{-# COMPILE GHC Vote = data G.Vote (G.MkVote) #-}
{-# COMPILE AGDA2HS iVoteEq #-}
```
```agda
record Postulates : Set₁ where
  field
    IsSlotLeader : PartyId → SlotNumber → LeadershipProof → Set
    IsCommitteeMember : PartyId → RoundNumber → MembershipProof → Set
    IsBlockSignature : Block → Signature → Set
    IsVoteSignature : Vote → Signature → Set

record Network : Set₁ where
  field
    Δ : Nat
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

{-# COMPILE AGDA2HS Chain #-}
```
```agda
certsFromChain : Chain → List Certificate
certsFromChain = mapMaybe certificate

{-# COMPILE AGDA2HS certsFromChain #-}
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
```agda
lastSlot : ∀ (c : Chain) → SlotNumber
lastSlot = foldr max (MkSlotNumber 0) ∘ map slotNumber

{-# COMPILE AGDA2HS lastSlot #-}
```
```agda
open Params ⦃...⦄
```

```agda
module _ ⦃ _ : Hashable Block ⦄
         where

  open Hashable ⦃...⦄

  cert₀ : Certificate
  cert₀ = MkCertificate (MkRoundNumber 0) (MkHash emptyBS)

  ChainExtends : Hash Block → Certificate → Chain → Set
  ChainExtends h c ch =
    Any (λ block → (hash block ≡ blockRef c))
      (dropWhile (λ block' → (hash block' /= h)) ch)

  Extends : Hash Block → Certificate → List Chain → Set
  Extends h c ch = if (c == cert₀) then ⊤ else Any (ChainExtends h c) ch
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
  pointsInto : Certificate → Chain → Bool
  pointsInto c ch = any (λ b → (blockRef c == hash b)) ch
```
```agda
  StartOfRound : SlotNumber → RoundNumber → Set
  StartOfRound (MkSlotNumber sl) (MkRoundNumber r) = sl ≡ r * U
```
```agda
  rnd : Nat → ⦃ _ : NonZero U ⦄ → Nat
  rnd s = s / U
```
```agda
  v-round : SlotNumber → RoundNumber
  v-round (MkSlotNumber s) = MkRoundNumber (rnd s)
```
### Chain weight

The weight of a chain is defined with respect of the Peras parameters

```agda
  weight : Chain → List Certificate → Nat
  weight ch cts = len ch + len (filter (flip pointsInto ch) cts) * B
    where
      len : ∀ {a : Set} → List a → Nat
      len = foldr (const suc) 0
```

### Chain validity

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
      → compare (lastSlot c) (slotNumber b) ≡ LT
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
