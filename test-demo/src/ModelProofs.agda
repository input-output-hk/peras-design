
module ModelProofs where

open import Data.Nat.Base using (ℕ; _%_)
open import Data.Product hiding (map)
open import Haskell.Prelude hiding (_×_; _×_×_; _,_,_; b; s) renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality

open import CommonTypes
open import Spec
open import Model

envState : State → EnvState
envState s = MkEnvState (Blk (lastBlock (aliceState s)))
                        (lastBlockSlot (aliceState s))
                        Alice
                        (clock s)

lem-produce : ∀ s → preProduceBlock (envState s) b ≡ True → ValidMessage (clock s) (aliceState s) Bob b
lem-produce = {!!}

lem-nextblock : ∀ s → preProduceBlock (envState s) b ≡ True → suc (lastBlock (aliceState s)) ≡ blockIndex b
lem-nextblock s = {!!}

lem-genesis : ∀ s → (time (envState s) == 0) ≡ True → SlotOf (clock s) Alice
lem-genesis s = {!!}

lem-whoseSlot : ∀ s → SlotOf (clock s) (whoseSlot (envState s))
lem-whoseSlot s = {!!}

-- TODO: more invariants:
--        - local states have correct lastBlock/lastBlockSlot
Invariant : State → Set
Invariant s = aliceState s ≡ bobState s

soundness : ∀ {env₁ bs} (s : State) (sig : Signal)
          → Invariant s
          → step (envState s) sig ≡ Just (env₁ ,, bs)
          → Σ State λ s₁ →
            Σ (happyPath ⊢ s ↝* s₁) λ trace →
              envState s₁ ≡ env₁
            × aliceMessages trace ≡ map (clock s ,_) bs
            × Invariant s₁
soundness s (ProduceBlock b) refl prf with preProduceBlock (envState s) b in eq
soundness s (ProduceBlock b) refl refl | True
  = ⟦ clock s , _ , _ ⟧
  , deliver (send {p = Bob} Alice b (correctMessage (lem-produce s eq)) λ())
            (receive (correctMessage (lem-produce s eq))) ∷ []
  , cong (λ i → MkEnvState (Blk i) _ _ _) (lem-nextblock s eq)
  , refl
  , refl
soundness s Tick refl prf with envSentBlock (envState s) in isEnvSlotAndSent
soundness s Tick refl refl | True
  = ⟦ suc (clock s) , _ , _ ⟧
  , tick (lem-whoseSlot s) {!!} ∷ []
  , refl
  , refl
  , refl
... | False with time (envState s) == 0 in isSlot0
soundness s Tick refl refl | False | True
  = ⟦ suc (clock s) , _ , _ ⟧
  , tick (lem-genesis s isSlot0) {!more invariants!!} ∷ []
  , refl
  , refl
  , refl
...   | False with whoseSlot (envState s) == Alice
...     | True = {!!}
