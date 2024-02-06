module Peras.Message where

open import Peras.Chain using (RoundNumber; Vote)

data Message msg : Set where
  VoteFor : RoundNumber → msg → Message msg
  NewVote : Vote msg → Message msg
  NewChain : msg → Message msg
