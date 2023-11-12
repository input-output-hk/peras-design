module Parameters where

open import Data.Nat
open import Data.List
open import Data.Bool

postulate Hash Party : Set

Slot = ℕ
SlotZero = 0
Delay = ℕ
Parties = List Party

postulate Winner : Party → Slot → Bool
