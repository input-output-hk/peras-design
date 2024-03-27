```agda
module Peras.Block where
```

<!--
```agda
open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (<-strictTotalOrder)
open import Data.List using (List)
open import Data.Unit using (⊤)
open import Level using (0ℓ)
open import Relation.Binary using (StrictTotalOrder; DecidableEquality)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Peras.Crypto

open import Haskell.Prelude using (Eq)
{-# FOREIGN AGDA2HS import Peras.Crypto (Hash (..), Hashable (..)) #-}
```
-->

## PartyId

```agda
PartyId = ℕ -- TODO: Data.Fin ?
```
<!--
```agda
{-# COMPILE AGDA2HS PartyId deriving (Eq) #-}
```
-->

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

<!--
```agda
{-# COMPILE AGDA2HS Party deriving Eq #-}
```
-->

## Honesty of a party

```agda
data Honesty : PartyId → Set where

  Honest : ∀ {p : PartyId}
    → Honesty p

  Corrupt : ∀ {p : PartyId}
    → Honesty p
```

## Transactions

```agda
Tx = ⊤
```

<!--
```agda
{-# COMPILE AGDA2HS Tx #-}
```
-->

## Slot

```agda
Slot = ℕ
```

<!--
```agda
{-# COMPILE AGDA2HS Slot #-}
```
-->

## Block and Certificate

In addition to a Praos block, there is an optional field for the included certificate.
**Note**: What we name `Block` is actually a block _Header_, we use `BlockBody` to contain the payload.

A Peras Certificate represents an aggregated quorum of votes for a specific block at a specific round.
Such a certificate is supposed to be self-contained and verifiable by any node.

```agda
record Block : Set
record BlockBody : Set
record Certificate : Set

record Certificate where
  field votingRoundNumber : ℕ
        blockRef : Hash Block

open Certificate public

record Block where
  field slotNumber : Slot
        creatorId : PartyId
        parentBlock : Hash Block
        certificate : Maybe Certificate
        leadershipProof : LeadershipProof
        signature : Signature
        bodyHash : Hash (List Tx)

open Block public

postulate
  _≟-Block_ : DecidableEquality Block

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
<!--
```agda
{-# COMPILE AGDA2HS Block deriving Eq #-}
{-# COMPILE AGDA2HS BlockBody deriving Eq #-}
{-# COMPILE AGDA2HS Certificate deriving Eq #-}
```
-->

```agda
private
  instance
    hashBlock : Hashable Block
    hashBlock = record
      { hash = λ b →
                 (let record { bytes = s } = signature b
                  in record { hashBytes = s })
      }

{-# COMPILE AGDA2HS hashBlock #-}
```
