```agda
module Peras.Block where
```

<!--
```agda
open import Haskell.Prelude

open import Data.Product using (∃; ∃-syntax)

open import Peras.Crypto
open import Peras.Numbering
open import Peras.Util

{-# FOREIGN AGDA2HS
{-# LANGUAGE DeriveGeneric #-}
import GHC.Generics (Generic)
import Peras.Crypto (Hash (..), Hashable (..))
import Prelude hiding (round)
#-}

{-# FOREIGN GHC
import qualified Peras.Block as G
#-}
```
-->

## PartyId

```agda
PartyId = Nat
```

<!--
```agda
{-# FOREIGN AGDA2HS
-- Use `Integer` for compatibility with `MAlonzo`.
type PartyId = Integer
#-}
```
-->

## Party

```agda
record Party : Set where
  constructor MkParty
  field pid : PartyId
        pkey : VerificationKey

open Party public

instance
  iPartyEq : Eq Party
  iPartyEq ._==_ x y = pid x == pid y && pkey x == pkey y
```

<!--
```agda
{-# COMPILE AGDA2HS Party deriving (Generic) #-}
{-# COMPILE GHC Party = data G.Party (G.MkParty) #-}
{-# COMPILE AGDA2HS iPartyEq #-}
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

```agda
PartyTup = ∃[ p ] (Honesty p)
Parties = List PartyTup
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

## Block and Certificate

In addition to a Praos block, there is an optional field for the included certificate.
**Note**: What we name `Block` is actually a block _Header_, we use `BlockBody` to contain the payload.

A Peras Certificate represents an aggregated quorum of votes for a specific block at a specific round.
Such a certificate is supposed to be self-contained and verifiable by any node.

```agda
record Block : Set
record BlockBody : Set
record Certificate : Set

Payload = List Tx

record Certificate where
  constructor MkCertificate
  pattern
  field round : RoundNumber
        blockRef : Hash Block

  roundNumber : Nat
  roundNumber = getRoundNumber round

open Certificate public

latestCert : Certificate → List Certificate → Certificate
latestCert c = maximumBy c (comparing round)

record Block where
  constructor MkBlock
  field slotNumber : SlotNumber
        creatorId : PartyId
        parentBlock : Hash Block
        certificate : Maybe Certificate
        leadershipProof : LeadershipProof
        signature : Signature
        bodyHash : Hash Payload

  slotNumber' : Nat
  slotNumber' = getSlotNumber slotNumber

open Block public

record BlockBody where
  constructor MkBlockBody
  field blockHash : Hash Payload
        payload : Payload

open BlockBody public
```
<!--
```agda
{-# COMPILE AGDA2HS Payload #-}
{-# COMPILE AGDA2HS Block deriving (Generic) #-}
{-# COMPILE GHC Block = data G.Block (G.MkBlock) #-}
{-# COMPILE AGDA2HS BlockBody deriving (Generic) #-}
{-# COMPILE GHC BlockBody = data G.BlockBody (G.MkBlockBody) #-}
{-# COMPILE AGDA2HS Certificate deriving (Generic) #-}
{-# COMPILE GHC Certificate = data G.Certificate (G.MkCertificate) #-}
```
-->

```agda
instance
  iCertificateEq : Eq Certificate
  iCertificateEq ._==_ x y = round x == round y && blockRef x == blockRef y

instance
  iBlockEq : Eq Block
  iBlockEq ._==_ x y = slotNumber x == slotNumber y
                         && creatorId x == creatorId y
                         && parentBlock x == parentBlock y
                         && leadershipProof x == leadershipProof y
                         && certificate x == certificate y
                         && signature x == signature y
                         && bodyHash x == bodyHash y
                         -- FIXME: In principle, we only need to check equality of the signatures.

instance
  iBlockBodyEq : Eq BlockBody
  iBlockBodyEq ._==_ x y = blockHash x == blockHash y && payload x == payload y

module _ {a : Set} ⦃ _ : Hashable a ⦄
  where

  open Hashable ⦃...⦄

  tipHash : List a → Hash a
  tipHash [] = MkHash emptyBS
  tipHash (x ∷ _) = hash x

private
  open Hashable
  instance
    hashBlock : Hashable Block
    hashBlock .hash = MkHash ∘ bytesS ∘ signature

{-# COMPILE AGDA2HS tipHash #-}
{-# COMPILE AGDA2HS iCertificateEq #-}
{-# COMPILE AGDA2HS iBlockEq #-}
{-# COMPILE AGDA2HS iBlockBodyEq #-}
{-# COMPILE AGDA2HS hashBlock #-}
```
