
-- The formal Agda specification with all the fancy types.

module Spec where

open import Data.Nat
open import Data.Nat.Properties
open import Data.List.Base
open import Data.Product.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Function

open import CommonTypes

-- Super simple protocol:
--  - The hosts take turns round robin to produce blocks.
--  - `blockIndex` is incremented with each block on the chain.
--  - If a node misses its window the other node should produce the missed block in its slot
--    instead.

record LocalState : Set where
  constructor _,_
  field
    lastBlock : BlockIndex
    lastBlockSlot : Slot

open LocalState public

record State : Set where
  constructor ⟦_,_,_⟧
  field
    clock        : Slot
    aliceState   : LocalState
    bobState     : LocalState

open State public

initLocalState : LocalState
initLocalState = 0 , 0

initState : State
initState = ⟦ 0 , initLocalState , initLocalState ⟧

getLocalState : Party → State → LocalState
getLocalState Alice = aliceState
getLocalState Bob   = bobState

modifyLocalState : Party → (LocalState → LocalState) → State → State
modifyLocalState Alice f ⟦ t , as , bs ⟧ = ⟦ t , f as , bs ⟧
modifyLocalState Bob   f ⟦ t , as , bs ⟧ = ⟦ t , as , f bs ⟧

setLocalState : Party → LocalState → State → State
setLocalState p ls = modifyLocalState p λ _ → ls

data Honesty : Set where
  happyPath : Honesty
  badAlice  : Honesty
  badBob    : Honesty

variable
  s s₀ s₁ s₂ : State
  ls ls₀ ls₁ : LocalState
  p q : Party
  b b₁ : Block
  i j : BlockIndex
  t t₁ : Slot
  @0 h : Honesty

data Dishonest : Honesty → Party → Set where
  badAlice : Dishonest badAlice Alice
  badBob   : Dishonest badBob   Bob

data SlotOf (t : Slot) : Party → Set where
  AliceSlot : t % 2 ≡ 0 → SlotOf t Alice
  BobSlot   : t % 2 ≡ 1 → SlotOf t Bob

data ValidMessage : Slot → LocalState → Party → Block → Set where
  valid : t < t₁ → SlotOf t₁ p → ValidMessage t₁ (i , t) p (Blk (suc i))

-- Local state update on receive
data _⊢_[_,_]?_ : Slot → LocalState → Party → Block → LocalState → Set where
  correctMessage : ValidMessage t₁ (i , t) p b → t₁ ⊢ (i , t) [ p , b ]? (suc i , t₁)
  wrongMessage   : ¬ ValidMessage t ls p b → t ⊢ ls [ p , b ]? ls

-- Message receive
data _[_,_↦_]?_ : State → Party → Block → Party → State → Set where
  receive : clock s ⊢ getLocalState q s [ p , b ]? ls →
            s [ p , b ↦ q ]? setLocalState q ls s

-- Local state update on send
data _,_,_⊢_[_↦_]!_ : Honesty → Slot → Party → LocalState → Block → Party → LocalState → Set where
  correctMessage   : ValidMessage t₁ (i , t) p b
                   → h , t₁ , p ⊢ (i , t) [ b ↦ q ]! (suc i , t₁)
  dishonestMessage : Dishonest h p
                   → h , t , p ⊢ ls [ b ↦ q ]! ls

-- Message send
data _⊢_[_,_↦_]!_ : Honesty → State → Party → Block → Party → State → Set where
  send : ∀ q b → h , clock s , p ⊢ getLocalState p s [ b ↦ q ]! ls
               → p ≢ q
               → h ⊢ s [ p , b ↦ q ]! setLocalState p ls s

data _⊢_↝_ : Honesty → State → State → Set where
  deliver : h ⊢ s₀ [ p , b ↦ q ]! s₁
          →     s₁ [ p , b ↦ q ]? s₂
          → h ⊢ s₀ ↝ s₂
  trickery : Dishonest h p → ∀ ls → h ⊢ s ↝ setLocalState p ls s
  tick     : SlotOf (clock s) p
           → lastBlockSlot (getLocalState p s) ≡ clock s
           → h ⊢ s ↝ record s { clock = suc (clock s) }

data _⊢_↝*_ : Honesty → State → State → Set where
  []  : h ⊢ s ↝* s
  _∷_ : h ⊢ s₀ ↝ s₁ → h ⊢ s₁ ↝* s₂ → h ⊢ s₀ ↝* s₂

messages : h ⊢ s₀ ↝* s₁ → List (Slot × Party × Block)
messages [] = []
messages {s₀ = s₀} (deliver {p = p} {b} _ _ ∷ tr) = (clock s₀ , p , b) ∷ messages tr
messages (trickery _ _ ∷ tr) = messages tr
messages (tick _ _ ∷ tr) = messages tr

aliceMessages : h ⊢ s₀ ↝* s₁ → List (Slot × Block)
aliceMessages [] = []
aliceMessages {s₀ = s₀} (deliver {p = Alice} {b} _ _ ∷ tr) = (clock s₀ , b) ∷ aliceMessages tr
aliceMessages (deliver _ _ ∷ tr) = aliceMessages tr
aliceMessages (trickery _ _ ∷ tr) = aliceMessages tr
aliceMessages (tick _ _ ∷ tr) = aliceMessages tr

-- Examples

_ : happyPath ⊢ initState ↝* ⟦ 2 , (2 , 2) , (2 , 2) ⟧
_ = tick (AliceSlot refl) refl
  ∷ deliver (send Alice (Blk 1) (correctMessage (valid ≤-refl (BobSlot refl))) λ())
            (receive (correctMessage (valid ≤-refl (BobSlot refl))))
  ∷ tick (BobSlot refl) refl
  ∷ deliver (send Bob (Blk 2) (correctMessage (valid ≤-refl (AliceSlot refl))) λ())
            (receive (correctMessage (valid ≤-refl (AliceSlot refl))))
  ∷ []

_ : badBob ⊢ initState ↝* ⟦ 2 , (1 , 2) , (1 , 2) ⟧
_ = tick (AliceSlot refl) refl
  ∷ trickery badBob (0 , 1)   -- Bob pretends to have sent a message (bumping lastBlkSlot)
  ∷ tick (BobSlot refl) refl
  ∷ deliver (send Bob (Blk 1) (correctMessage (valid (s≤s z≤n) (AliceSlot refl))) λ())
            (receive (correctMessage (valid ≤-refl (AliceSlot refl))))
  ∷ []
