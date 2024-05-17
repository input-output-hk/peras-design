```agda
module Peras.Numbering where
```

<!--
```agda
open import Data.Nat using (ℕ; pred; suc; _∸_; _*_)
open import Data.Nat.Properties using (_≟_)
open import Function.Base using (_∘_)
open import Haskell.Prelude using (Eq; _==_;  cong)
open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary using (¬_; yes; no)

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
```

<!--
```agda
{-# FOREIGN AGDA2HS
-- Use `Integer` for compatibility with `MAlonzo`.
newtype SlotNumber = MkSlotNumber {getSlotNumber :: Integer}
  deriving (Generic)
#-}

{-# COMPILE GHC SlotNumber = data G.SlotNumber (G.MkSlotNumber) #-}

{-# COMPILE AGDA2HS iSlotNumberEq #-}
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
```

<!--
```agda
{-# FOREIGN AGDA2HS
-- Use `Integer` for compatibility with `MAlonzo`.
newtype RoundNumber = MkRoundNumber {getRoundNumber :: Integer}
  deriving (Generic)
#-}

{-# COMPILE GHC RoundNumber = data G.RoundNumber (G.MkRoundNumber) #-}

{-# COMPILE AGDA2HS iRoundNumberEq #-}
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
```
