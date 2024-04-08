
-- Computational model that we can compile to Haskell and hook up with
-- a QuickCheck Dynamic state model. Proofs that it matches the Spec.

module Model where

open import Data.Nat.Base using (ℕ; _%_)
open import Haskell.Prelude

open import CommonTypes
open import Spec

{-# FOREIGN AGDA2HS
import GHC.Generics
#-}

instance
  EqParty : Eq Party
  EqParty ._==_ Alice Alice = True
  EqParty ._==_ Alice Bob   = False
  EqParty ._==_ Bob Alice   = False
  EqParty ._==_ Bob Bob     = True

  EqBlock : Eq Block
  EqBlock ._==_ (Blk i) (Blk j) = i == j

data Signal : Set where
  ProduceBlock : Block → Signal
  Tick : Signal

{-# COMPILE AGDA2HS Signal deriving (Eq, Ord, Show, Generic) #-}

record EnvState : Set where
  constructor MkEnvState
  field
    lastBlock : Block
    lastBlockTime : Slot
    sutParty : Party
    time : Slot

open EnvState public

{-# COMPILE AGDA2HS EnvState deriving (Eq, Ord, Show, Generic) #-}

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

preProduceBlock : EnvState → Block → Bool
preProduceBlock s b =
     nextBlock s == b
  && whoseSlot s == envParty s
  && not (lastBlockTime s == time s)

{-# COMPILE AGDA2HS preProduceBlock #-}

envSentBlock : EnvState → Bool
envSentBlock s =
  whoseSlot s == envParty s &&
  lastBlockTime s == time s

{-# COMPILE AGDA2HS envSentBlock #-}

step : EnvState → Signal → Maybe (EnvState × List Block)
step s (ProduceBlock b) =
  if preProduceBlock s b
  then Just (record s { lastBlock = b; lastBlockTime = time s } , [])
  else Nothing
step s Tick =
  if envSentBlock s
  then Just (record s { time = 1 + time s } , [])
  else if time s == 0
  then Just (record s { time = 1 + time s } , [])
  else if whoseSlot s == sutParty s
  then Just ( record s { time = 1 + time s
                      ; lastBlock = nextBlock s
                      ; lastBlockTime = time s
                      }
            , nextBlock s ∷ [])
  else Nothing

{-# COMPILE AGDA2HS step #-}
