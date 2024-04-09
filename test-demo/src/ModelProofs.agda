
module ModelProofs where

open import Data.Nat.Base using (ℕ; _%_; _≤_; s≤s; z≤n) renaming (_<_ to _<ℕ_)
open import Data.Nat.Properties
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Haskell.Prelude hiding (_×_; _×_×_; _,_,_; b; s; t; ⊥) renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality
open import Data.Empty

open import CommonTypes
open import Spec
open import Model

variable
  A : Set
  env : EnvState

envState : State → EnvState
envState s = MkEnvState (Blk (lastBlock (aliceState s)))
                        (lastBlockSlot (aliceState s))
                        Alice
                        (clock s)

ltℕ-sound : ∀ {n m} → (n < m) ≡ True → n <ℕ m
ltℕ-sound {zero}  {suc m} h = s≤s z≤n
ltℕ-sound {suc n} {suc m} h = s≤s (ltℕ-sound h)

opaque
  unfolding preProduceBlock

  decomp-preProduce₁ : preProduceBlock env b ≡ True → nextBlock env ≡ b
  decomp-preProduce₁ h = eqBlock-sound (&&ˡ h)

  decomp-preProduce₂ : preProduceBlock env b ≡ True → SlotOf (time env) (envParty env)
  decomp-preProduce₂ {env = env} {b = b} h = lem-whoseSlot env (eqParty-sound (&&ˡ (&&ʳ {nextBlock env == b} h)))

  decomp-preProduce₃ : preProduceBlock env b ≡ True → lastBlockTime env <ℕ time env
  decomp-preProduce₃ {env = env} {b = b} h = ltℕ-sound (&&ʳ (&&ʳ {nextBlock env == b} h))

lem-produce : ∀ s → preProduceBlock (envState s) b ≡ True → ValidMessage (clock s) (aliceState s) Bob b
lem-produce s h with refl ← decomp-preProduce₁ h = valid (decomp-preProduce₃ h) (decomp-preProduce₂ h)

lem-nextblock : ∀ s → preProduceBlock (envState s) b ≡ True → suc (lastBlock (aliceState s)) ≡ blockIndex b
lem-nextblock s h with refl ← decomp-preProduce₁ h = refl

slotOf-deterministic : SlotOf t Alice → SlotOf t Bob → ⊥
slotOf-deterministic (AliceSlot is0) (BobSlot is1) rewrite is0 = case is1 of λ ()

tickAfterSend : A ⊎ SlotOf t Bob → SlotOf t Alice → A
tickAfterSend (inj₁ p) _ = p
tickAfterSend (inj₂ bob) alice = ⊥-elim (slotOf-deterministic alice bob)

record Invariant (s : State) : Set where
  constructor inv
  field
    localStatesAgree   : aliceState s ≡ bobState s
    causality          : lastBlockSlot (aliceState s) ≤ clock s
    tickAfterAliceSend : lastBlockSlot (aliceState s) <ℕ clock s ⊎ SlotOf (clock s) Bob

record Soundness (h : Honesty) (s : State) (endEnv : EnvState) (bs : List Block) : Set where
  field
    endState  : State
    invariant : Invariant endState
    trace     : h ⊢ s ↝* endState
    envOk     : envState endState ≡ endEnv
    blocksOk  : aliceMessages trace ≡ map (clock s ,_) bs

open Soundness

@0 soundness : ∀ {env₁ bs} (s : State) (sig : Signal happyPath)
          → Invariant s
          → step (envState s) sig ≡ Just (env₁ ,, bs)
          → Soundness h s env₁ bs
soundness s (ProduceBlock b) (inv refl _ _) prf with preProduceBlock (envState s) b in eq
soundness s (ProduceBlock b) (inv refl _ _) refl | True = record
  { endState  = ⟦ clock s , _ , _ ⟧
  ; invariant = inv refl ≤-refl (inj₂ (decomp-preProduce₂ eq))
  ; trace     = deliver (send {p = Bob} Alice b (correctMessage (lem-produce s eq)) λ())
                        (receive (correctMessage (lem-produce s eq))) ∷ []
  ; envOk     = cong (λ i → MkEnvState (Blk i) _ _ _) (lem-nextblock s eq)
  ; blocksOk  = refl
  }
-- soundness s (DishonestProduceBlock b) (inv refl _ _) prf with preProduceBlock (envState s) b in eq
-- soundness s (DishonestProduceBlock b) (inv refl _ _) refl | False = record
--   { endState  = ⟦ clock s , _ , _ ⟧
--   ; invariant = inv refl {!!} {!!}
--   ; trace     = {!!}
--   ; envOk     = {!!}
--   ; blocksOk  = {!!}
--   }
soundness s Tick (inv refl _ _) prf with whenTick (envState s)
soundness s Tick (inv refl z≤n _) refl | GenesisTick refl = record
  { endState  = ⟦ 1 , _ , _ ⟧
  ; invariant = inv refl z≤n (inj₂ (BobSlot refl))
  ; trace     = tick (AliceSlot refl) refl ∷ []
  ; envOk     = refl
  ; blocksOk  = refl
  }
soundness s Tick (inv refl _ _) refl | TickAfterEnvSend isEnvSlot refl = record
  { endState  = ⟦ suc (clock s) , _ , _ ⟧
  ; invariant = inv refl (n≤1+n _) (inj₁ ≤-refl)
  ; trace     = tick isEnvSlot refl
              ∷ []
  ; envOk     = refl
  ; blocksOk  = refl
  }
soundness s Tick (inv refl _ slotInv) refl | SutSendAndTick isAliceSlot = record
  { endState  = ⟦ suc (clock s) , _ , _ ⟧
  ; invariant = inv refl (n≤1+n _) (inj₁ ≤-refl)
  ; trace     = let b = nextBlock (envState s)
                    validB : ValidMessage (clock s) (aliceState s) Alice b
                    validB = valid (tickAfterSend slotInv isAliceSlot) isAliceSlot
                in deliver (send {p = Alice} Bob b
                                 (correctMessage validB) λ())
                           (receive (correctMessage validB))
                 ∷ tick isAliceSlot refl
                 ∷ []
  ; envOk     = refl
  ; blocksOk  = refl
  }
