{-# LANGUAGE DeriveGeneric #-}

module Peras.Numbering where

import GHC.Generics (Generic)

instance Eq SlotNumber where
  x == y = getSlotNumber x == getSlotNumber y

-- Use `Integer` for compatibility with `MAlonzo`.
newtype SlotNumber = MkSlotNumber {getSlotNumber :: Integer}
  deriving (Generic)

instance Eq RoundNumber where
  x == y = getRoundNumber x == getRoundNumber y

-- Use `Integer` for compatibility with `MAlonzo`.
newtype RoundNumber = MkRoundNumber {getRoundNumber :: Integer}
  deriving (Generic)
