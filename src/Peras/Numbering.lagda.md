```agda
module Peras.Numbering where
```

<!--
```agda
open import Agda.Builtin.FromNat
open import Data.Nat using (ℕ; pred; suc; _+_; _∸_; _*_; _/_; _%_; NonZero)
open import Data.Nat.Properties using (_≟_)
open import Data.Unit using (⊤)
open import Function.Base using (_∘_)
open import Haskell.Prelude using (Eq; Ord; ordFromCompare; compare; _==_;  cong)
open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary using (¬_; yes; no)
open import Peras.Abstract.Protocol.Params
open import Peras.Util

{-# FOREIGN AGDA2HS
{-# LANGUAGE DeriveGeneric #-}
import GHC.Generics (Generic)
#-}

{-# FOREIGN GHC
import qualified Peras.Numbering as G
#-}
```
-->

## Slots

```agda
record SlotNumber : Set where
  constructor MkSlotNumber
  field getSlotNumber : ℕ

  next : SlotNumber
  next = record {getSlotNumber = suc getSlotNumber}

  _earlierBy_  : ℕ → SlotNumber
  _earlierBy_ n = record {getSlotNumber = getSlotNumber ∸ n}

open SlotNumber public

instance
  iSlotNumberEq : Eq SlotNumber
  iSlotNumberEq ._==_ x y = getSlotNumber x == getSlotNumber y

  iSlotNumberOrd : Ord SlotNumber
  iSlotNumberOrd = ordFromCompare λ x y → compare (getSlotNumber x) (getSlotNumber y)

  iNumberSlotNumber : Number SlotNumber
  iNumberSlotNumber .Number.Constraint _ = ⊤
  iNumberSlotNumber .fromNat n = MkSlotNumber n
```

<!--
```agda
{-# FOREIGN AGDA2HS
-- Use `Integer` for compatibility with `MAlonzo`.
newtype SlotNumber = MkSlotNumber {getSlotNumber :: Integer}
  deriving (Generic, Eq, Ord, Read, Show)
#-}

{-# COMPILE GHC SlotNumber = data G.SlotNumber (G.MkSlotNumber) #-}
```
-->

## Rounds

```agda
record RoundNumber : Set where
  constructor MkRoundNumber
  field getRoundNumber : ℕ

  prev : RoundNumber
  prev = record { getRoundNumber = pred getRoundNumber }

open RoundNumber public

instance
  iRoundNumberEq : Eq RoundNumber
  iRoundNumberEq ._==_ x y = getRoundNumber x == getRoundNumber y

  iRoundNumberOrd : Ord RoundNumber
  iRoundNumberOrd = ordFromCompare λ x y → compare (getRoundNumber x) (getRoundNumber y)

  iNumberRoundNumber : Number RoundNumber
  iNumberRoundNumber .Number.Constraint _ = ⊤
  iNumberRoundNumber .fromNat n = MkRoundNumber n
```

<!--
```agda
{-# FOREIGN AGDA2HS
-- Use `Integer` for compatibility with `MAlonzo`.
newtype RoundNumber = MkRoundNumber {getRoundNumber :: Integer}
  deriving (Generic, Eq, Ord, Read, Show)
#-}

{-# COMPILE GHC RoundNumber = data G.RoundNumber (G.MkRoundNumber) #-}

private
  div : ℕ → (n : ℕ) → @0 ⦃ NonZero n ⦄ → ℕ
  div a b ⦃ prf ⦄ = _/_ a b ⦃ uneraseNonZero prf ⦄

private
  mod : ℕ → (n : ℕ) → @0 ⦃ NonZero n ⦄ → ℕ
  mod a b ⦃ prf ⦄ = _%_ a b ⦃ uneraseNonZero prf ⦄
```
-->

```agda
_≟-RoundNumber_ : DecidableEquality RoundNumber
(MkRoundNumber r₁) ≟-RoundNumber (MkRoundNumber r₂) with r₁ ≟ r₂
... | yes p = yes (cong MkRoundNumber p)
... | no ¬p =  no (¬p ∘ cong getRoundNumber)

```

```agda
roundToSlot : ℕ → RoundNumber → SlotNumber
roundToSlot T (MkRoundNumber r) = MkSlotNumber (r * T)

slotToRound : PerasParams → SlotNumber → RoundNumber
slotToRound protocol (MkSlotNumber n) = MkRoundNumber (div n (perasU protocol))

slotInRound : PerasParams → SlotNumber → SlotNumber
slotInRound protocol slot = MkSlotNumber (mod (getSlotNumber slot) (perasU protocol))

nextSlot : SlotNumber → SlotNumber
nextSlot (MkSlotNumber n) = MkSlotNumber (1 + n)

nextRound : RoundNumber → RoundNumber
nextRound (MkRoundNumber n) = MkRoundNumber (1 + n)
```

<!--
```agda
{-# COMPILE AGDA2HS slotToRound #-}
{-# COMPILE AGDA2HS slotInRound #-}
{-# COMPILE AGDA2HS nextSlot #-}
{-# COMPILE AGDA2HS nextRound #-}
```
-->
