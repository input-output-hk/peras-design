
module ModelProofs where

open import Data.Nat.Base using (ℕ; _%_; _≤_; s≤s; z≤n) renaming (_<_ to _<ℕ_)
open import Data.Nat.Properties
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Haskell.Prelude hiding (_×_; _×_×_; _,_,_; b; s; t; ⊥) renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty

open import CommonTypes
open import Spec
open import Model

variable
  A : Set
  env : EnvState
  bs : List Block

envState : State → EnvState
envState s = MkEnvState (Blk (lastBlock (aliceState s)))
                        (lastBlockSlot (aliceState s))
                        Alice
                        (clock s)

ltℕ-sound : ∀ {n m} → (n < m) ≡ True → n <ℕ m
ltℕ-sound {zero}  {suc m} h = s≤s z≤n
ltℕ-sound {suc n} {suc m} h = s≤s (ltℕ-sound h)

ltℕ-complete : ∀ {n m} → (n < m) ≡ False → ¬ (n <ℕ m)
ltℕ-complete {suc n} {suc m} h (s≤s lt) = ltℕ-complete {n} {m} h lt

opaque
  unfolding preProduceBlock

  decomp-preProduce₁ : preProduceBlock env b ≡ True → nextBlock env ≡ b
  decomp-preProduce₁ h = eqBlock-sound (&&ˡ h)

  decomp-preProduce₂ : preProduceBlock env b ≡ True → SlotOf (time env) (envParty env)
  decomp-preProduce₂ {env = env} {b = b} h =
    lem-whoseSlot env (eqParty-sound (&&ˡ (&&ʳ {nextBlock env == b} h)))

  decomp-preProduce₃ : preProduceBlock env b ≡ True → lastBlockTime env <ℕ time env
  decomp-preProduce₃ {env = env} {b = b} h = ltℕ-sound (&&ʳ (&&ʳ {nextBlock env == b} h))

data NotPreProduceBlock (env : EnvState) (b : Block) : Set where
  wrongBlock    : nextBlock env ≢ b → NotPreProduceBlock env b
  wrongProducer : ¬ SlotOf (time env) (envParty env) → NotPreProduceBlock env b
  alreadySent   : ¬ (lastBlockTime env <ℕ time env) → NotPreProduceBlock env b

opaque
  unfolding preProduceBlock

  decomp-!preProduce : preProduceBlock env b ≡ False → NotPreProduceBlock env b
  decomp-!preProduce {env = env} {b} h with !&& {nextBlock env == b} h
  ... | inj₁ p₁ = wrongBlock (eqBlock-complete p₁)
  ... | inj₂ q with !&& {whoseSlot env == envParty env} q
  ...   | inj₁ p₂ = wrongProducer λ bobSlot → eqParty-complete p₂ (whoseSlot-complete env bobSlot)
  ...   | inj₂ p₃ = alreadySent (ltℕ-complete p₃)

opaque
  unfolding preDishonestTick

  decomp-preDishonestTick₁ : preDishonestTick env ≡ True → SlotOf (time env) (envParty env)
  decomp-preDishonestTick₁ {env = env} h = lem-whoseSlot env (eqParty-sound (&&ˡ h))

  decomp-preDishonestTick₂ : preDishonestTick env ≡ True → lastBlockTime env <ℕ time env
  decomp-preDishonestTick₂ h = ltℕ-sound (&&ʳ h)

lem-produce : ∀ s → preProduceBlock (envState s) b ≡ True → ValidMessage (clock s) (aliceState s) Bob b
lem-produce s h with refl ← decomp-preProduce₁ h = valid (decomp-preProduce₃ h) (decomp-preProduce₂ h)

lem-dishonest-produce : ∀ s → preProduceBlock (envState s) b ≡ False
                            → ¬ ValidMessage (clock s) (aliceState s) Bob b
lem-dishonest-produce s h (valid p q) with decomp-!preProduce h
... | wrongBlock p₁    = p₁ refl
... | wrongProducer p₂ = p₂ q
... | alreadySent p₃   = p₃ p

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

liftSoundness : Soundness happyPath s env bs → Soundness h s env bs
liftSoundness s = record
  { endState  = endState s
  ; invariant = invariant s
  ; trace     = liftHonesty* (trace s)
  ; envOk     = envOk s
  ; blocksOk  = trans (sym $ sameAliceMessages (trace s)) (blocksOk s)
  }

@0 honest-soundness : ∀ {env₁ bs} (s : State) (sig : Signal happyPath)
          → Invariant s
          → step (envState s) sig ≡ Just (env₁ ,, bs)
          → Soundness happyPath s env₁ bs
honest-soundness s (ProduceBlock b) (inv refl _ _) prf with preProduceBlock (envState s) b in eq
honest-soundness s (ProduceBlock b) (inv refl _ _) refl | True = record
  { endState  = ⟦ clock s , _ , _ ⟧
  ; invariant = inv refl ≤-refl (inj₂ (decomp-preProduce₂ eq))
  ; trace     = deliver (send {p = Bob} Alice b (correctMessage (lem-produce s eq)) λ())
                        (receive (correctMessage (lem-produce s eq))) ∷ []
  ; envOk     = cong (λ i → MkEnvState (Blk i) _ _ _) (lem-nextblock s eq)
  ; blocksOk  = refl
  }
honest-soundness s Tick (inv refl _ _) prf with whenTick (envState s)
honest-soundness s Tick (inv refl z≤n _) refl | GenesisTick refl = record
  { endState  = ⟦ 1 , _ , _ ⟧
  ; invariant = inv refl z≤n (inj₂ (BobSlot refl))
  ; trace     = tick (AliceSlot refl) refl ∷ []
  ; envOk     = refl
  ; blocksOk  = refl
  }
honest-soundness s Tick (inv refl _ _) refl | TickAfterEnvSend isEnvSlot refl = record
  { endState  = ⟦ suc (clock s) , _ , _ ⟧
  ; invariant = inv refl (n≤1+n _) (inj₁ ≤-refl)
  ; trace     = tick isEnvSlot refl
              ∷ []
  ; envOk     = refl
  ; blocksOk  = refl
  }
honest-soundness s Tick (inv refl _ slotInv) refl | SutSendAndTick isAliceSlot = record
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

@0 soundness : ∀ {env₁ bs} (s : State) (sig : Signal h)
          → Invariant s
          → step (envState s) sig ≡ Just (env₁ ,, bs)
          → Soundness h s env₁ bs
soundness s (ProduceBlock b) i prf          = liftSoundness (honest-soundness s (ProduceBlock b) i prf)
soundness s Tick i prf                      = liftSoundness (honest-soundness s Tick i prf)
soundness s (DishonestProduceBlock b) (inv refl _ _) prf with preProduceBlock (envState s) b in eq
soundness s (DishonestProduceBlock b) i@(inv refl _ _) refl | False = record
  { endState  = s
  ; invariant = i
  ; trace     = deliver (send Alice b (dishonestMessage badBob) λ())
                        (receive (wrongMessage (lem-dishonest-produce s eq)))
              ∷ []
  ; envOk     = refl
  ; blocksOk  = refl
  }
soundness s DishonestTick (inv refl _ _) prf with preDishonestTick (envState s) in eq
soundness s DishonestTick (inv refl lt _) refl | True = record
  { endState  = ⟦ suc (clock s) , aliceState s , _ ⟧
  ; invariant = inv refl (m≤n⇒m≤1+n lt) (inj₁ (s≤s lt))
  ; trace     = trickery badBob (record (aliceState s) { lastBlockSlot = clock s })
              ∷ tick (decomp-preDishonestTick₁ eq) refl
              ∷ trickery badBob (aliceState s)
              ∷ []
  ; envOk     = refl
  ; blocksOk  = refl
  }
