module Peras.Message where
{-# FOREIGN AGDA2HS
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE DerivingStrategies #-}
#-}

-- import Peras.Chain (RoundNumber, Vote)
open import Peras.Chain

data Message msg : Set where
  VoteFor : RoundNumber → msg → Message msg
  NewVote : Vote msg → Message msg
  NewChain : msg → Message msg
{-# COMPILE AGDA2HS Message deriving (Eq, Show) #-}
-- stock deriving strategy not supported
