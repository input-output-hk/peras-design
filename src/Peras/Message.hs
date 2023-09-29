{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE DerivingStrategies #-}
module Peras.Message where
import Peras.Chain (RoundNumber, Vote)


data Message msg
  = VoteFor {round :: RoundNumber, message :: msg}
  | NewVote {vote :: Vote msg}
  | NewChain {block :: msg}
  deriving stock (Eq, Show)
