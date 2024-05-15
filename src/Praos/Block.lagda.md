```agda
module Praos.Block where
```

<!--
```agda
open import Data.Bool using (Bool; true; false)
open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (<-strictTotalOrder)
open import Data.Product using (∃-syntax)
open import Data.Unit using (⊤)
open import Level using (0ℓ)
open import Relation.Binary using (StrictTotalOrder; DecidableEquality)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_)

open import Praos.Crypto
```
-->

## PartyId

```agda
PartyId = ℕ -- TODO: Data.Fin ?
```

The party identifier needs to be strictly, totally ordered to be used as key

```agda
PartyIdO : StrictTotalOrder 0ℓ 0ℓ 0ℓ
PartyIdO = <-strictTotalOrder
```

## Party

```agda
record Party : Set where
  constructor MkParty
  field id : PartyId
        vkey : VerificationKey

open Party public
```

## Honesty of a party

```agda
data Honesty : PartyId → Set where

  Honest : ∀ {p : PartyId}
    → Honesty p

  Corrupt : ∀ {p : PartyId}
    → Honesty p
```
```agda
PartyTup = ∃[ p ] (Honesty p)
Parties = List PartyTup
```
```agda
postulate
  Honest≢Corrupt : ∀ {p₁ p₂} {h₁ : Honesty p₁} {h₂ : Honesty p₂}
    → h₁ ≡ Honest
    → h₂ ≡ Corrupt
    → p₁ ≢ p₂

isHonest : ∀ {p : PartyId} → Honesty p → Bool
isHonest {p} Honest = true
isHonest {p} Corrupt = false
```

## Transactions

```agda
Tx = ⊤
```

## Slot

```agda
Slot = ℕ
```

## Block

```agda
record Block : Set
record BlockBody : Set

record Block where
  field slotNumber : Slot
        creatorId : PartyId
        parentBlock : Hash Block
        leadershipProof : LeadershipProof
        signature : Signature
        bodyHash : Hash (List Tx)

open Block public

postulate
  _≟-Block_ : DecidableEquality Block
  _≟-BlockHash_ : DecidableEquality (Hash Block)

record BlockBody where
  field blockHash : Hash (List Tx)
        payload : List Tx

open BlockBody public
```
```agda
data HonestBlock : Block → Set where

  HonestParty : ∀ {p : PartyId} {h : Honesty p} {b : Block}
    → creatorId b ≡ p
    → h ≡ Honest {p}
    → HonestBlock b
```
