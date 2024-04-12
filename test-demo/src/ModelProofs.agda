
module ModelProofs where

open import Data.Nat.Base using (ℕ; _%_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.List using (_++_)
open import Haskell.Prelude hiding (_×_; _×_×_; _,_,_; b; s; t; ⊥; _<>_; _++_) renaming (_,_ to _,ʰ_; _<_ to _<ʰ_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty

open import CommonTypes
open import ProofPrelude
open import FormalSpec
open import TestModel

variable
  A             : Set
  env env₁ env₂ : EnvState
  bs bs₁        : List Block
  ms ms₁        : List (Slot × Block)
  sig           : Signal h
  sigs          : List (Signal h)

envState : State → EnvState
envState s = record
  { lastBlock     = lastBlock (aliceState s)
  ; lastBlockTime = lastBlockSlot (aliceState s)
  ; sutParty      = Alice
  ; time          = clock s
  }

module _ (h : produceBlockOk env b ≡ True) where
  opaque
    unfolding produceBlockOk

    produceOk⇒isNextBlock : nextBlock env ≡ b
    produceOk⇒isNextBlock = eqBlock-sound (&&ˡ h)

    produceOk⇒envSlot : SlotOf (time env) (envParty env)
    produceOk⇒envSlot =
      lem-whoseSlot env (eqParty-sound (&&ˡ (&&ʳ {nextBlock env == b} h)))

    produceOk⇒noBlockThisSlot : lastBlockTime env < time env
    produceOk⇒noBlockThisSlot = ltℕ-sound (&&ʳ (&&ʳ {nextBlock env == b} h))

data ProduceBlockNotOk (env : EnvState) (b : Block) : Set where
  wrongBlock    : nextBlock env ≢ b → ProduceBlockNotOk env b
  wrongProducer : ¬ SlotOf (time env) (envParty env) → ProduceBlockNotOk env b
  alreadySent   : ¬ (lastBlockTime env < time env) → ProduceBlockNotOk env b

opaque
  unfolding produceBlockOk

  whyProduceBlockNotOk : produceBlockOk env b ≡ False → ProduceBlockNotOk env b
  whyProduceBlockNotOk {env = env} {b} h with !&& {nextBlock env == b} h
  ... | inj₁ p₁ = wrongBlock (eqBlock-complete p₁)
  ... | inj₂ q with !&& {whoseSlot env == envParty env} q
  ...   | inj₁ p₂ = wrongProducer λ bobSlot → eqParty-complete p₂ (whoseSlot-complete env bobSlot)
  ...   | inj₂ p₃ = alreadySent (ltℕ-complete p₃)

opaque
  unfolding dishonestTickOk

  dishonestTickOk⇒envSlot : dishonestTickOk env ≡ True → SlotOf (time env) (envParty env)
  dishonestTickOk⇒envSlot {env = env} h = lem-whoseSlot env (eqParty-sound (&&ˡ h))

  dishonestTickOk⇒noBlockThisSlot : dishonestTickOk env ≡ True → lastBlockTime env < time env
  dishonestTickOk⇒noBlockThisSlot h = ltℕ-sound (&&ʳ h)

produceOk⇒validBlock : ∀ s → produceBlockOk (envState s) b ≡ True → ValidBlock (clock s) (aliceState s) Bob b
produceOk⇒validBlock s h with refl ← produceOk⇒isNextBlock h = valid (produceOk⇒noBlockThisSlot h) (produceOk⇒envSlot h)

produceNotOk⇒invalidBlock : ∀ s → produceBlockOk (envState s) b ≡ False
                            → ¬ ValidBlock (clock s) (aliceState s) Bob b
produceNotOk⇒invalidBlock s h (valid p q) with whyProduceBlockNotOk h
... | wrongBlock p₁    = p₁ refl
... | wrongProducer p₂ = p₂ q
... | alreadySent p₃   = p₃ p

slotOf-deterministic : SlotOf t Bob → SlotOf t Alice → ⊥
slotOf-deterministic (BobSlot is1) (AliceSlot is0) rewrite is0 = case is1 of λ ()

record Invariant (s : State) : Set where
  constructor inv
  field
    localStatesAgree   : aliceState s ≡ bobState s
    causality          : lastBlockSlot (aliceState s) ≤ clock s
    tickAfterAliceSend : SlotOf (clock s) Alice → lastBlockSlot (aliceState s) < clock s

record Soundness (h : Honesty) (s : State) (endEnv : EnvState) (bs : List (Slot × Block)) : Set where
  field
    endState   : State
    invariant₀ : Invariant s
    invariant₁ : Invariant endState
    trace      : h ⊢ s ↝* endState
    envOk      : envState endState ≡ endEnv
    blocksOk   : aliceBlocks trace ≡ bs

open Soundness

liftSoundness : Soundness happyPath s env ms → Soundness h s env ms
liftSoundness s = record
  { endState   = endState s
  ; invariant₀ = invariant₀ s
  ; invariant₁ = invariant₁ s
  ; trace      = liftHonesty* (trace s)
  ; envOk      = envOk s
  ; blocksOk   = trans (sym $ sameAliceBlocks (trace s)) (blocksOk s)
  }

@0 honest-soundness : ∀ {env₁ bs} (s : State) (sig : Signal happyPath)
          → Invariant s
          → step (envState s) sig ≡ Just (env₁ ,ʰ bs)
          → Soundness happyPath s env₁ (map (clock s ,_) bs)
honest-soundness s (ProduceBlock b) (inv refl _ _) prf with produceBlockOk (envState s) b in eq
honest-soundness s (ProduceBlock b) i@(inv refl _ _) refl | True = case produceOk⇒validBlock s eq of λ where
  v@(valid _ _) → record
    { endState  = ⟦ clock s , _ , _ ⟧
    ; invariant₀ = i
    ; invariant₁ = inv refl ≤-refl (⊥-elim ∘ slotOf-deterministic (produceOk⇒envSlot eq))
    ; trace     = deliver (send {p = Bob} Alice b (correctBlock v) λ())
                          (receive (correctBlock v)) ∷ []
    ; envOk     = refl
    ; blocksOk  = refl
    }
honest-soundness s Tick (inv refl _ _) prf with whenTick (envState s)
honest-soundness s Tick i@(inv refl z≤n _) refl | GenesisTick refl = record
  { endState   = ⟦ 1 , _ , _ ⟧
  ; invariant₀ = i
  ; invariant₁ = inv refl z≤n λ _ → s≤s z≤n
  ; trace      = tick (AliceSlot refl) refl ∷ []
  ; envOk      = refl
  ; blocksOk   = refl
  }
honest-soundness s Tick i@(inv refl _ _) refl | TickAfterEnvSend isEnvSlot refl = record
  { endState   = ⟦ suc (clock s) , _ , _ ⟧
  ; invariant₀ = i
  ; invariant₁ = inv refl (n≤1+n _) λ _ → ≤-refl
  ; trace      = tick isEnvSlot refl
               ∷ []
  ; envOk      = refl
  ; blocksOk   = refl
  }
honest-soundness s Tick i@(inv refl _ slotInv) refl | SutSendAndTick isAliceSlot = record
  { endState   = ⟦ suc (clock s) , _ , _ ⟧
  ; invariant₀ = i
  ; invariant₁ = inv refl (n≤1+n _) λ _ → ≤-refl
  ; trace      = let b = nextBlock (envState s)
                     validB : ValidBlock (clock s) (aliceState s) Alice b
                     validB = valid (slotInv isAliceSlot) isAliceSlot
                 in deliver (send {p = Alice} Bob b
                                  (correctBlock validB) λ())
                            (receive (correctBlock validB))
                  ∷ tick isAliceSlot refl
                  ∷ []
  ; envOk      = refl
  ; blocksOk   = refl
  }

@0 soundness : ∀ {env₁ bs} (s : State) (sig : Signal h)
             → Invariant s
             → step (envState s) sig ≡ Just (env₁ ,ʰ bs)
             → Soundness h s env₁ (map (clock s ,_) bs)
soundness s (ProduceBlock b) i prf = liftSoundness (honest-soundness s (ProduceBlock b) i prf)
soundness s Tick i prf             = liftSoundness (honest-soundness s Tick i prf)
soundness s (DishonestProduceBlock b) (inv refl _ _) prf with produceBlockOk (envState s) b in eq
soundness s (DishonestProduceBlock b) i@(inv refl _ _) refl | False = record
  { endState   = s
  ; invariant₀ = i
  ; invariant₁ = i
  ; trace      = deliver (send Alice b (dishonestBlock badBob) λ())
                         (receive (wrongBlock (produceNotOk⇒invalidBlock s eq)))
               ∷ []
  ; envOk      = refl
  ; blocksOk   = refl
  }
soundness s DishonestTick (inv refl _ _) prf with dishonestTickOk (envState s) in eq
soundness s DishonestTick i@(inv refl lt _) refl | True = record
  { endState   = ⟦ suc (clock s) , aliceState s , _ ⟧
  ; invariant₀ = i
  ; invariant₁ = inv refl (m≤n⇒m≤1+n lt) (λ _ → s≤s lt)
  ; trace      = trickery badBob (record (aliceState s) { lastBlockSlot = clock s })
               ∷ tick (dishonestTickOk⇒envSlot eq) refl
               ∷ trickery badBob (aliceState s)
               ∷ []
  ; envOk      = refl
  ; blocksOk   = refl
  }

data ValidActions h (env : EnvState) : EnvState → List (Signal h) → List (Slot × Block) → Set where
  []  : ValidActions h env env [] []
  ⟨_,_⟩∷_ : (sig : Signal h)
          → step env sig ≡ Just (env₁ ,ʰ bs)
          → ValidActions h env₁ env₂ sigs ms₁ → ValidActions h env env₂ (sig ∷ sigs) (map (time env ,_) bs ++ ms₁)

open ≡-Reasoning

appendSoundness : Soundness h s (envState s₁) ms
                → Soundness h s₁ env₁ ms₁
                → Soundness h s env₁ (ms ++ ms₁)
appendSoundness {s = s} {s₁ = s₁} {ms = ms} {ms₁ = ms₁}
                sound₁@record{trace = tr₁; invariant₁ = inv refl _ _; envOk = refl}
                sound₂@record{trace = tr₂; invariant₀ = inv refl _ _} = record
  { trace      = sound₁ .trace <> sound₂ .trace
  ; invariant₀ = sound₁ .invariant₀
  ; invariant₁ = sound₂ .invariant₁
  ; envOk      = sound₂ .envOk
  ; blocksOk   = begin
      aliceBlocks (tr₁ <> tr₂)           ≡⟨ appendAliceBlocks tr₁ tr₂ ⟩
      aliceBlocks tr₁ ++ aliceBlocks tr₂ ≡⟨ cong₂ _++_ (sound₁ .blocksOk) (sound₂ .blocksOk) ⟩
      ms ++ ms₁
    ∎
  }

@0 soundness* : Invariant s → (as : ValidActions h (envState s) env₁ sigs ms) → Soundness h s env₁ ms
soundness* i [] = record
  { invariant₀ = i
  ; invariant₁ = i
  ; trace      = []
  ; envOk      = refl
  ; blocksOk   = refl
  }
soundness* i (⟨ sig , ok ⟩∷ as) = case soundness _ sig i ok of λ where
  sound₁@record { invariant₁ = i₁; envOk = refl } →
    appendSoundness sound₁ (soundness* i₁ as)

-- Some thoughts about completeness.

-- Informally we would like to prove that for any trace s ↝* s₁ we can
-- construct a sequence of signals that produces an equivalent trace from
-- the point of view of Alice.
-- Aside from being very hard to state formally nevermind prove, this
-- property is also not true. Why not? Because in an arbitrary trace
-- Bob can send a dishonest message after Alice sends her message.

-- record AliceStateEquivalence (s₁ s₂ : State) : Set where

-- data AliceTraceEquivalence (r : h ⊢ s₁ ↝* s₂) (r₁ : h ⊢ s₃ ↝* s₄) : Set where

-- record Completeness (i : Invariant s) (r : h ⊢ s ↝* s₁) : Set where
--   field
--     {actions}    : List (Signal h)
--     validActions : ValidActions h (envState s) actions
--     prf          : AliceTraceEquivalence r (trace (soundness* i validActions))

-- completeness : (i : Invariant s) (r : h ⊢ s ↝* s₁) → Completeness i r
-- completeness tr = {!!}
