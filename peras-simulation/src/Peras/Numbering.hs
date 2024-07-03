{-# LANGUAGE DeriveGeneric #-}

module Peras.Numbering where

import Peras.Conformance.Params (PerasParams (perasU))

import GHC.Generics (Generic)

-- Use `Integer` for compatibility with `MAlonzo`.
newtype SlotNumber = MkSlotNumber {getSlotNumber :: Integer}
  deriving (Generic, Eq, Ord, Read, Show)

-- Use `Integer` for compatibility with `MAlonzo`.
newtype RoundNumber = MkRoundNumber {getRoundNumber :: Integer}
  deriving (Generic, Eq, Ord, Read, Show)

slotToRound :: PerasParams -> SlotNumber -> RoundNumber
slotToRound protocol (MkSlotNumber n) =
  MkRoundNumber (div n (perasU protocol))

slotInRound :: PerasParams -> SlotNumber -> SlotNumber
slotInRound protocol slot =
  MkSlotNumber (mod (getSlotNumber slot) (perasU protocol))

nextSlot :: SlotNumber -> SlotNumber
nextSlot (MkSlotNumber n) = MkSlotNumber (1 + n)

nextRound :: RoundNumber -> RoundNumber
nextRound (MkRoundNumber n) = MkRoundNumber (1 + n)
