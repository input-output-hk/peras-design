module MessageTuple where

open import Data.List

open import Parameters
open import Message

record MessageTuple : Set where
  field msg : Message
        rcv : Party
        cd  : Delay

MessagePool = List Message 
