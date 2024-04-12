
-- The formal Agda specification with all the fancy types.

module FormalSpec where

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
-- Network model: π-calculus style instant delivery

record LocalState : Set where
  constructor _,_
  field
    lastBlock     : Block
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
initLocalState = Blk 0 , 0

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
  s s₀ s₁ s₂ s₃ s₄ : State
  ls ls₀ ls₁       : LocalState
  p q              : Party
  b b₁             : Block
  i j              : BlockIndex
  t t₁             : Slot
  @0 h             : Honesty

data Dishonest : Honesty → Party → Set where
  badAlice : Dishonest badAlice Alice
  badBob   : Dishonest badBob   Bob

data SlotOf (t : Slot) : Party → Set where
  AliceSlot : t % 2 ≡ 0 → SlotOf t Alice
  BobSlot   : t % 2 ≡ 1 → SlotOf t Bob

data ValidBlock : Slot → LocalState → Party → Block → Set where
  valid : t < t₁ → SlotOf t₁ p → ValidBlock t₁ (Blk i , t) p (Blk (suc i))

-- Local state update on receive
data _⊢_[_,_]?_ : Slot → LocalState → Party → Block → LocalState → Set where
  correctBlock : ValidBlock t₁ (Blk i , t) p b → t₁ ⊢ (Blk i , t) [ p , b ]? (Blk (suc i) , t₁)
  wrongBlock   : ¬ ValidBlock t ls p b → t ⊢ ls [ p , b ]? ls

-- Block receive
data _[_,_↦_]?_ : State → Party → Block → Party → State → Set where
  receive : clock s ⊢ getLocalState q s [ p , b ]? ls →
            s [ p , b ↦ q ]? setLocalState q ls s

-- Local state update on send
data _,_,_⊢_[_↦_]!_ : Honesty → Slot → Party → LocalState → Block → Party → LocalState → Set where
  correctBlock   : ValidBlock t₁ (Blk i , t) p b
                   → h , t₁ , p ⊢ (Blk i , t) [ b ↦ q ]! (Blk (suc i) , t₁)
  dishonestBlock : Dishonest h p
                   → h , t , p ⊢ ls [ b ↦ q ]! ls

-- Block send
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

infixr 5 _<>_
_<>_ : h ⊢ s₀ ↝* s₁ → h ⊢ s₁ ↝* s₂ → h ⊢ s₀ ↝* s₂
[]       <> tr = tr
(r ∷ tr) <> tr₁ = r ∷ tr <> tr₁

messages : h ⊢ s₀ ↝* s₁ → List (Slot × Party × Block)
messages [] = []
messages {s₀ = s₀} (deliver {p = p} {b} _ _ ∷ tr) = (clock s₀ , p , b) ∷ messages tr
messages (trickery _ _ ∷ tr) = messages tr
messages (tick _ _ ∷ tr) = messages tr

aliceBlocks : h ⊢ s₀ ↝* s₁ → List (Slot × Block)
aliceBlocks [] = []
aliceBlocks {s₀ = s₀} (deliver {p = Alice} {b} _ _ ∷ tr) = (clock s₀ , b) ∷ aliceBlocks tr
aliceBlocks (deliver _ _ ∷ tr) = aliceBlocks tr
aliceBlocks (trickery _ _ ∷ tr) = aliceBlocks tr
aliceBlocks (tick _ _ ∷ tr) = aliceBlocks tr

-- Some proofs

liftHonesty : happyPath ⊢ s ↝ s₁ → h ⊢ s ↝ s₁
liftHonesty (deliver (send q b (correctBlock v) !q) r) = deliver (send q b (correctBlock v) !q) r
liftHonesty (tick sl sent) = tick sl sent

liftHonesty* : happyPath ⊢ s ↝* s₁ → h ⊢ s ↝* s₁
liftHonesty* []       = []
liftHonesty* (r ∷ tr) = liftHonesty r ∷ liftHonesty* tr

sameAliceBlocks : (tr : happyPath ⊢ s ↝* s₁) → aliceBlocks tr ≡ aliceBlocks (liftHonesty* {h = h} tr)
sameAliceBlocks [] = refl
sameAliceBlocks {h = h} (deliver {p = Alice} {b} (send _ _ (correctBlock _) _) _ ∷ tr)
  rewrite sameAliceBlocks {h = h} tr = refl
sameAliceBlocks (deliver {p = Bob} (send _ _ (correctBlock _) _) _ ∷ tr) = sameAliceBlocks tr
sameAliceBlocks (tick _ _ ∷ tr) = sameAliceBlocks tr

appendAliceBlocks : (tr : h ⊢ s₀ ↝* s₁) (tr₁ : h ⊢ s₁ ↝* s₂) → aliceBlocks (tr <> tr₁) ≡ aliceBlocks tr ++ aliceBlocks tr₁
appendAliceBlocks []       tr₁ = refl
appendAliceBlocks (deliver {p = Alice} _ _ ∷ tr) tr₁ rewrite appendAliceBlocks tr tr₁ = refl
appendAliceBlocks (deliver {p = Bob  } _ _ ∷ tr) tr₁ = appendAliceBlocks tr tr₁
appendAliceBlocks (trickery _ _ ∷ tr)            tr₁ = appendAliceBlocks tr tr₁
appendAliceBlocks (tick _ _ ∷ tr)                tr₁ = appendAliceBlocks tr tr₁

-- Examples

_ : happyPath ⊢ initState ↝* ⟦ 2 , (Blk 2 , 2) , (Blk 2 , 2) ⟧
_ = tick (AliceSlot refl) refl
  ∷ deliver (send Alice (Blk 1) (correctBlock (valid ≤-refl (BobSlot refl))) λ())
            (receive (correctBlock (valid ≤-refl (BobSlot refl))))
  ∷ tick (BobSlot refl) refl
  ∷ deliver (send Bob (Blk 2) (correctBlock (valid ≤-refl (AliceSlot refl))) λ())
            (receive (correctBlock (valid ≤-refl (AliceSlot refl))))
  ∷ []

_ : badBob ⊢ initState ↝* ⟦ 2 , (Blk 1 , 2) , (Blk 1 , 2) ⟧
_ = tick (AliceSlot refl) refl
  ∷ trickery badBob (Blk 0 , 1)   -- Bob pretends to have sent a message (bumping lastBlkSlot)
  ∷ tick (BobSlot refl) refl
  ∷ deliver (send Bob (Blk 1) (correctBlock (valid (s≤s z≤n) (AliceSlot refl))) λ())
            (receive (correctBlock (valid ≤-refl (AliceSlot refl))))
  ∷ []
