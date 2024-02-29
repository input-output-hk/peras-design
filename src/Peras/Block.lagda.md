```agda
module Peras.Block where
```

<!--
```agda
open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (<-strictTotalOrder)
open import Data.List using (List)
open import Data.Unit using (⊤)
open import Level using (0ℓ)
open import Relation.Binary using (StrictTotalOrder)

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

## Block

```agda
record Block : Set where
  field slotNumber : Slot
        creatorId : PartyId
        parentBlock : Hash
        includedVotes : List Hash
        leadershipProof : LeadershipProof
        payload : List Tx
        signature : Signature

open Block public
```

<!--
```agda
{-# COMPILE AGDA2HS Block deriving Eq #-}
```
-->

```agda
private
  instance
    hashBlock : Hashable Block
    hashBlock = record
      { hash = λ b →
                 (let record { bytes = s } = signature b
                  in record { bs = s })
      }

{-# COMPILE AGDA2HS hashBlock #-}
```
