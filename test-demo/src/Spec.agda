
-- The formal Agda specification with all the fancy types.

module Spec where

open import Data.Nat
open import Data.List.Base
open import Data.Product.Base
open import Relation.Binary.PropositionalEquality

-- Super simple protocol:
--  - The hosts take turns round robin to produce blocks.
--  - `blockIndex` is incremented with each block on the chain.
--  - If a node misses its window the other node should produce the missed block in its slot
--    instead.

data Party : Set where
  alice bob : Party

BlockIndex = ℕ

data Block : Set where
  block : BlockIndex → Block

record Message : Set where
  field
    messageBlock      : Block
    messageOriginator : Party

record LocalState : Set where
  constructor ⟦_⟧
  field
    lastSeen : BlockIndex

Slot = ℕ

record State : Set where
  constructor ⟦_,_,_⟧
  field
    clock        : Slot
    messageQueue : List (Party × Message)
    aliceState   : LocalState
    bobState     : LocalState

open State

modifyLocalState : Party → (LocalState → LocalState) → State → State
modifyLocalState alice f s = record s { aliceState = f (aliceState s) }
modifyLocalState bob   f s = record s { bobState   = f (bobState   s) }

variable
  s s₀ s₁ : State
  ls ls₀ ls₁ : LocalState
  p : Party
  m : Message
  b b₁ : BlockIndex

-- Message delivery
data _[_]→_ : LocalState → Block → LocalState → Set where
  correctBlock : ⟦ b ⟧ [ block (suc b) ]→ ⟦ suc b ⟧
  wrongBlock   : suc b ≢ b₁ → ⟦ b ⟧ [ block b₁ ]→ ⟦ b ⟧

data _[_]↷_ : State → Party × Message → State → Set where

data _↝_ : State → State → Set where
  deliver : s₀ [ p , m ]↷ s₁ → s₀ ↝ s₁
