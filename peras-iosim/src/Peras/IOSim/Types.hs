{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Types (
  ByteSize,
  Coin,
  Round,
  Vote,
  Votes,
) where

import GHC.Generics (Generic)
import Peras.Block (Block, PartyId)
import Peras.Orphans ()

import qualified Data.Aeson as A
import qualified Data.Set as S

type Coin = Int

type Round = Word

type ByteSize = Word

type Votes = S.Set Vote

data Vote = Vote
  { votingRound :: Round
  , voter :: PartyId
  , block :: Block Votes
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance A.FromJSON Vote where
  parseJSON =
    A.withObject "Vote" $
      \o ->
        do
          votingRound <- o A..: "round"
          voter <- o A..: "voter"
          block <- o A..: "block"
          pure Vote{..}

instance A.ToJSON Vote where
  toJSON Vote{..} =
    A.object
      [ "round" A..= votingRound
      , "voter" A..= voter
      , "block" A..= block
      ]
