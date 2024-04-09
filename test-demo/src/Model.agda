
-- Computational model that we can compile to Haskell and hook up with
-- a QuickCheck Dynamic state model. Proofs that it matches the Spec.

module Model where

open import Data.Nat.Base using (ℕ; _%_)
open import Data.Sum
open import Haskell.Prelude
open import Relation.Binary.PropositionalEquality

open import CommonTypes
open import Spec

{-# FOREIGN AGDA2HS
import GHC.Generics
#-}

it : {A : Set} → ⦃ A ⦄ → A
it ⦃ x ⦄ = x

-- Boolean shenanigans

&&ˡ : ∀ {a b : Bool} → (a && b) ≡ True → a ≡ True
&&ˡ {True} _ = refl

&&ʳ : ∀ {a b : Bool} → (a && b) ≡ True → b ≡ True
&&ʳ {True} {True} _ = refl

!&& : ∀ {a b : Bool} → (a && b) ≡ False → a ≡ False ⊎ b ≡ False
!&& {False}        _ = inj₁ refl
!&& {True} {False} _ = inj₂ refl

not-elim : ∀ {a} → not a ≡ True → a ≡ False
not-elim {False} _ = refl

instance
  EqParty : Eq Party
  EqParty ._==_ Alice Alice = True
  EqParty ._==_ Alice Bob   = False
  EqParty ._==_ Bob Alice   = False
  EqParty ._==_ Bob Bob     = True

  EqBlock : Eq Block
  EqBlock ._==_ (Blk i) (Blk j) = i == j

eqℕ-sound : {t t₁ : Slot} → (t == t₁) ≡ True → t ≡ t₁
eqℕ-sound {zero}  {zero}   _   = refl
eqℕ-sound {suc t} {suc t₁} prf = cong suc (eqℕ-sound prf)

eqℕ-complete : {t t₁ : Slot} → (t == t₁) ≡ False → t ≢ t₁
eqℕ-complete {suc t} isF refl = eqℕ-complete {t} isF refl

eqParty-sound : (p == q) ≡ True → p ≡ q
eqParty-sound {Alice} {Alice} _ = refl
eqParty-sound {Bob}   {Bob}   _ = refl

eqParty-complete : (p == q) ≡ False → p ≢ q
eqParty-complete {Alice} {Bob} h ()
eqParty-complete {Bob} {Alice} h ()

eqBlock-sound : ∀ {b b₁ : Block} → (b == b₁) ≡ True → b ≡ b₁
eqBlock-sound {Blk i} {Blk j} h = cong Blk (eqℕ-sound h)

eqBlock-complete : ∀ {b b₁ : Block} → (b == b₁) ≡ False → b ≢ b₁
eqBlock-complete {Blk i} isF refl = eqℕ-complete {i} isF refl

data Signal : (@0 h : Honesty) → Set where
  ProduceBlock : Block → Signal h
  DishonestProduceBlock : Block → Signal badBob
  Tick : Signal h
  DishonestTick : Signal badBob
{-# COMPILE AGDA2HS Signal deriving (Eq, Ord, Show, Generic) #-}

record EnvState : Set where
  constructor MkEnvState
  field
    lastBlock : Block
    lastBlockTime : Slot
    sutParty : Party
    time : Slot
{-# COMPILE AGDA2HS EnvState deriving (Eq, Ord, Show, Generic) #-}

open EnvState public

startingState : EnvState
startingState = record { lastBlock = Blk 0
                       ; lastBlockTime = 0
                       ; sutParty = Alice
                       ; time = 0
                       }
{-# COMPILE AGDA2HS startingState #-}

even : ℕ → Bool
even n = n % 2 == 0

envParty : EnvState → Party
envParty record{ sutParty = Alice } = Bob
envParty record{ sutParty = Bob   } = Alice
{-# COMPILE AGDA2HS envParty #-}

nextBlock : EnvState → Block
nextBlock s = Blk (1 + blockIndex (lastBlock s))
{-# COMPILE AGDA2HS nextBlock #-}

whoseSlot : EnvState → Party
whoseSlot s = if even (time s) then Alice else Bob
{-# COMPILE AGDA2HS whoseSlot #-}

opaque
  preProduceBlock : EnvState → Block → Bool
  preProduceBlock s b =
       nextBlock s == b
    && whoseSlot s == envParty s
    && lastBlockTime s < time s
  {-# COMPILE AGDA2HS preProduceBlock #-}

envSentBlock : EnvState → Bool
envSentBlock s =
  whoseSlot s == envParty s &&
  lastBlockTime s == time s
{-# COMPILE AGDA2HS envSentBlock #-}

tickSlot : EnvState → EnvState
tickSlot s = record s { time = 1 + time s }
{-# COMPILE AGDA2HS tickSlot #-}

data WhenTick (@0 s : EnvState) : Set where
  GenesisTick      : @0 time s ≡ 0 → WhenTick s
  TickAfterEnvSend : @0 SlotOf (time s) (envParty s)
                   → @0 lastBlockTime s ≡ time s
                   → WhenTick s
  SutSendAndTick   : @0 SlotOf (time s) (sutParty s) → WhenTick s
  NoTick           : WhenTick s
{-# COMPILE AGDA2HS WhenTick #-}

lem-whoseSlot : ∀ s {p} → whoseSlot s ≡ p → SlotOf (time s) p
lem-whoseSlot s refl with time s % 2 in eq
... | 0   = AliceSlot eq
... | 1   = BobSlot eq
... | hm? = yeah-no
  where postulate yeah-no : SlotOf _ _

whoseSlot-complete : ∀ s {p} → SlotOf (time s) p → whoseSlot s ≡ p
whoseSlot-complete s (AliceSlot eq) rewrite eq = refl
whoseSlot-complete s (BobSlot   eq) rewrite eq = refl

opaque
  whenTick : (s : EnvState) → WhenTick s
  whenTick s =
         if envSentBlock s            then TickAfterEnvSend (lem-whoseSlot s (eqParty-sound (&&ˡ it))) (eqℕ-sound (&&ʳ it))
    else if time s == 0               then GenesisTick (eqℕ-sound it)
    else if whoseSlot s == sutParty s then SutSendAndTick (lem-whoseSlot s (eqParty-sound it))
    else NoTick
  {-# COMPILE AGDA2HS whenTick #-}

stepTick : (s : EnvState) → WhenTick s → Maybe (EnvState × List Block)
stepTick s (TickAfterEnvSend _ _) = Just (tickSlot s , [])
stepTick s (GenesisTick _)        = Just (tickSlot s , [])
stepTick s (SutSendAndTick _)     = Just ( tickSlot record s
                                                    { lastBlock     = nextBlock s
                                                    ; lastBlockTime = time s
                                                    }
                                         , nextBlock s ∷ [])
stepTick _ NoTick                 = Nothing
{-# COMPILE AGDA2HS stepTick #-}

opaque
  preDishonestTick : EnvState → Bool
  preDishonestTick s = whoseSlot s == envParty s && lastBlockTime s < time s
  {-# COMPILE AGDA2HS preDishonestTick #-}

step : EnvState → Signal h → Maybe (EnvState × List Block)
step s (ProduceBlock b) =
  if preProduceBlock s b
  then Just (record s { lastBlock = b; lastBlockTime = time s } , [])
  else Nothing
step s (DishonestProduceBlock b) =
  if preProduceBlock s b
  then Nothing
  else Just (s , [])
step s Tick = stepTick s (whenTick s)
step s DishonestTick =
  if preDishonestTick s
  then Just (tickSlot s , [])
  else Nothing
{-# COMPILE AGDA2HS step #-}
