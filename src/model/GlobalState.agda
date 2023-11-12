module GlobalState where

open import Data.List
open import Data.Maybe

open import Parameters
open import Message
open import MessageTuple
open import LocalState

StateMap = Party → Maybe LocalState
postulate AdversarialState : Set

History = List Message


record GlobalState : Set₁ where
  field tNow : Slot
        msgBuff : MessagePool
        stateMap : StateMap
        history : History
        advState : AdversarialState
        execOrder : Parties
