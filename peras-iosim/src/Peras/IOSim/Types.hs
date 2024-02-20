{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Types (
  ByteSize,
  Coin,
  Round,
  Vote (..),
  Votes,
) where

import Data.Function (on)
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import Peras.Block (Block, PartyId)
import Peras.Crypto (Signature)
import Peras.Orphans ()

import qualified Data.Aeson as A
import qualified Data.Set as S

type Coin = Int

type Round = Natural

type ByteSize = Word

type Votes = S.Set Vote

data Vote = Vote
  { votingRound :: Round
  , voteSignature :: Signature
  , voteForBlock :: Block Votes
  , voter :: PartyId
  }
  deriving stock (Generic, Read, Show)

instance Eq Vote where
  (==) = (==) `on` voteSignature

instance Ord Vote where
  compare = compare `on` voteSignature

instance A.FromJSON Vote where
  parseJSON =
    A.withObject "Vote" $
      \o ->
        do
          votingRound <- o A..: "round"
          voteSignature <- o A..: "signature"
          voter <- o A..: "voter"
          voteForBlock <- o A..: "block"
          pure Vote{..}

instance A.ToJSON Vote where
  toJSON Vote{..} =
    A.object
      [ "round" A..= votingRound
      , "signature" A..= voteSignature
      , "voter" A..= voter
      , "block" A..= voteForBlock
      ]
