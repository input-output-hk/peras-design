
-- Computational model that we can compile to Haskell and hook up with
-- a QuickCheck Dynamic state model. Proofs that it matches the Spec.

module TestModel where

open import Data.Nat.Base using (ℕ; _%_)
open import Data.Sum
open import Haskell.Prelude
open import Relation.Binary.PropositionalEquality

open import CommonTypes
open import ProofPrelude
open import FormalSpec hiding (h)

{-# FOREIGN AGDA2HS
import GHC.Generics
#-}

variable
  @0 h : Honesty  -- We want to erase Honesty parameters in the Haskell code

data Signal : (@0 h : Honesty) → Set where
  ProduceBlock          : Block → Signal h
  DishonestProduceBlock : Block → Signal badBob
  Tick                  : Signal h
  DishonestTick         : Signal badBob
{-# COMPILE AGDA2HS Signal deriving (Eq, Ord, Show, Generic) #-}

record EnvState : Set where
  constructor MkEnvState
  field
    lastBlock     : Block
    lastBlockTime : Slot
    sutParty      : Party
    time          : Slot
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
  produceBlockOk : EnvState → Block → Bool
  produceBlockOk s b =
       nextBlock s == b
    && whoseSlot s == envParty s
    && lastBlockTime s < time s
  {-# COMPILE AGDA2HS produceBlockOk #-}

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
         if envSentBlock s            then TickAfterEnvSend (lem-whoseSlot s (eqParty-sound (&&ˡ it)))
                                                            (eqℕ-sound (&&ʳ it))
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
  dishonestTickOk : EnvState → Bool
  dishonestTickOk s = whoseSlot s == envParty s && lastBlockTime s < time s
  {-# COMPILE AGDA2HS dishonestTickOk #-}

step : EnvState → Signal h → Maybe (EnvState × List Block)
step s (ProduceBlock b) =
  if produceBlockOk s b
  then Just (record s { lastBlock = b; lastBlockTime = time s } , [])
  else Nothing
step s (DishonestProduceBlock b) =
  if produceBlockOk s b
  then Nothing
  else Just (s , [])
step s Tick = stepTick s (whenTick s)
step s DishonestTick =
  if dishonestTickOk s
  then Just (tickSlot s , [])
  else Nothing
{-# COMPILE AGDA2HS step #-}
