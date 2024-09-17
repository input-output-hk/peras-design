```agda
module Peras.Block where
```

<!--
```agda
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; null; head; filter)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Maybe using (Maybe; maybe′; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (<-strictTotalOrder)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Function using (_∘_)
open import Haskell.Prelude as Haskell using (Eq; _==_; True; False; _&&_)
open import Level using (0ℓ)
open import Relation.Binary using (StrictTotalOrder; DecidableEquality)
open import Relation.Nullary using (yes; no; ¬_)

open import Data.Nat.Properties using (≤-totalOrder)
open import Data.List.Extrema (≤-totalOrder) using (argmax)

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; cong₂)

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
PartyId = ℕ  -- FIXME: Data.Fin ?
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
  iPartyEq .Haskell._==_ x y = pid x Haskell.== pid y && pkey x Haskell.== pkey y
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

  roundNumber : ℕ
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

  slotNumber' : ℕ
  slotNumber' = getSlotNumber slotNumber

open Block public

_≟-BlockHash_ : DecidableEquality (Hash Block)
(MkHash b₁) ≟-BlockHash (MkHash b₂) with b₁ ≟-BS b₂
... | yes p = yes (cong MkHash p)
... | no ¬p =  no (¬p ∘ cong hashBytes)

_≟-Certificate_ : DecidableEquality Certificate
(MkCertificate r₁ b₁) ≟-Certificate (MkCertificate r₂ b₂)
  with r₁ ≟-RoundNumber r₂
  with b₁ ≟-BlockHash b₂
... | yes p | yes q = yes (cong₂ MkCertificate p q)
... | _ | no ¬q = no (¬q ∘ cong blockRef)
... | no ¬p | _ = no (¬p ∘ cong round)

record BlockBody where
  constructor MkBlockBody
  field blockHash : Hash Payload
        payload : Payload

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
{-# COMPILE AGDA2HS Payload #-}
{-# COMPILE AGDA2HS Block deriving (Generic) #-}
{-# COMPILE GHC Block = data G.Block (G.MkBlock) #-}
{-# COMPILE AGDA2HS BlockBody deriving (Generic) #-}
{-# COMPILE GHC BlockBody = data G.BlockBody (G.MkBlockBody) #-}
{-# COMPILE AGDA2HS Certificate deriving (Generic) #-}
{-# COMPILE GHC Certificate = data G.Certificate (G.MkCertificate) #-}

instance
  iMaybeEq : {a : Set} → ⦃ i : Eq a ⦄ → Eq (Maybe a)
  iMaybeEq {{i}} ._==_ x y =
    maybe′
      (λ x' → maybe′ (λ y' → x' == y') False y)
      (maybe′ (λ _ → False) True y)
      x
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
  tipHash Data.List.[] = MkHash emptyBS
  tipHash (x Data.List.∷ _) = hash x

{-# COMPILE AGDA2HS tipHash #-}

private
  open Hashable

  instance
    hashBlock : Hashable Block
    hashBlock .hash = MkHash ∘ bytesS ∘ signature
```

<!--
```agda
{-# COMPILE AGDA2HS iCertificateEq #-}
{-# COMPILE AGDA2HS iBlockEq #-}
{-# COMPILE AGDA2HS iBlockBodyEq #-}

{-# COMPILE AGDA2HS hashBlock #-}
```
-->
