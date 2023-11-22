{-
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE DerivingStrategies #-}
-}
module Peras.Message where

-- import Peras.Chain (RoundNumber, Vote)
open import Peras.Chain

data Message msg : Set where
  VoteFor : RoundNumber → msg → Message msg
  NewVote : Vote msg → Message msg
  NewChain : msg → Message msg
  -- deriving stock (Eq, Show)
