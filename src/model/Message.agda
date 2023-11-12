module Message where

open import Data.List

open import Block

data Message : Set where
  BlockMsg : Block → Message

Messages = List Message
