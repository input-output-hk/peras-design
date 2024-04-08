
module CommonTypes where

open import Data.Nat.Base

{-# FOREIGN AGDA2HS import GHC.Generics #-}

data Party : Set where
  Alice Bob : Party

{-# COMPILE AGDA2HS Party deriving (Eq, Ord, Show, Generic) #-}

BlockIndex = ℕ
Slot = ℕ

{-# FOREIGN AGDA2HS
type BlockIndex = Integer
type Slot = Integer
#-}

record Block : Set where
  constructor Blk
  field
    blockIndex : BlockIndex

open Block public

{-# COMPILE AGDA2HS Block deriving (Eq, Ord, Show, Generic) #-}
