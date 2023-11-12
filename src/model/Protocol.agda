module Protocol where

open import Data.Unit
open import Data.Product

open import Parameters
open import Block
open import Message
open import LocalState

-- these should be defined
postulate honestMint : Slot → Transactions → LocalState → Messages × LocalState
postulate honestReceive : Messages → Slot → LocalState → ⊤ × LocalState
