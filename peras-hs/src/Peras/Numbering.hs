{-# LANGUAGE DeriveGeneric #-}

module Peras.Numbering where


import GHC.Generics (Generic)

-- Use `Integer` for compatibility with `MAlonzo`.
newtype SlotNumber = MkSlotNumber {getSlotNumber :: Integer}
  deriving (Generic, Eq, Ord, Read, Show)

-- Use `Integer` for compatibility with `MAlonzo`.
newtype RoundNumber = MkRoundNumber {getRoundNumber :: Integer}
  deriving (Generic, Eq, Ord, Read, Show)

