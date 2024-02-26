{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Types (
  ByteSize,
  Coin,
  Rollback (..),
  Round,
  Vote (..),
  Votes,
) where

import Data.Function (on)
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import Peras.Block (Block, PartyId, Slot)
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

data Rollback = Rollback
  { atSlot :: Slot
  , slots :: Int
  , blocks :: Int
  , fromWeight :: Double
  , toWeight :: Double
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance A.FromJSON Rollback where
  parseJSON =
    A.withObject "Rollback" $
      \o ->
        do
          atSlot <- o A..: "atSlot"
          slots <- o A..: "slots"
          blocks <- o A..: "blocks"
          fromWeight <- o A..: "fromWeight"
          toWeight <- o A..: "toWeight"
          pure Rollback{..}

instance A.ToJSON Rollback where
  toJSON Rollback{..} =
    A.object
      [ "atSlot" A..= atSlot
      , "slots" A..= slots
      , "blocks" A..= blocks
      , "fromWeight" A..= fromWeight
      , "toWeight" A..= toWeight
      ]
