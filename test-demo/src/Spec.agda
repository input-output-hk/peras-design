
-- The formal Agda specification with all the fancy types.

module Spec where

open import Data.Nat
open import Data.List.Base
open import Data.Product.Base

-- Some kind of non-determinstic transition system.
-- Hierarchical (system/nodes)

data Party : Set where
  alice bob : Party

data Message : Set where
  ping pong : Message

NodeState : Set
NodeState = ℕ

record State : Set where
  constructor ⟦_,_,_⟧
  field
    messageQueue : List (Party × Message)
    aliceState   : NodeState
    bobState     : NodeState

variable
  s s₀ s₁ : State
  p : Party
  m : Message

-- Message delivery
data _[_]↷_ : State → Party × Message → State → Set where

data _↝_ : State → State → Set where
  deliver : s₀ [ p , m ]↷ s₁ → s₀ ↝ s₁
