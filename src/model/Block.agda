module Block where

open import Data.List
open import Parameters

postulate Transaction : Set

Transactions = List Transaction

record Block : Set where
  constructor MkBlock
  field sl : Slot
        txs : Transactions
        pred : Hash
        bid  : Party
open Block public

Chain = List Block
Chains = List Chain
BlockPool = List Block

-- paramemeters(?)
postulate GenesisBlock : Block
          HashB : Block → Hash
