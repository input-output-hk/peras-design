{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Peras.Abstract.Protocol.Trace where

import Control.Tracer (Tracer (..), contramap, stdoutTracer)
import Data.Aeson (FromJSON, ToJSON, object, (.=))
import qualified Data.Aeson as A
import Data.Set (Set, toList)
import Data.Text (Text)
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.Encoding as LE
import GHC.Generics (Generic)
import Peras.Block (Block, Certificate, PartyId)
import Peras.Chain (Chain, Vote (..))
import Peras.Crypto (Hash)
import Peras.Numbering (RoundNumber, SlotNumber)
import Peras.Orphans ()

data PerasLog
  = Tick {slot :: SlotNumber, roundNumber :: RoundNumber}
  | NewChainAndVotes {newChains :: Set Chain, newVotes :: Set Vote}
  | NewChainPref {newChainPref :: Chain}
  | NewCertificatesReceived {newCertificates :: [(Certificate, SlotNumber)]}
  | NewCertificatesFromQuorum {newQuorums :: [Certificate]}
  | NewCertPrime {newCertPrime :: Certificate}
  | NewCertStar {newCertStar :: Certificate}
  | CastVote {vote :: Vote}
  deriving stock (Show, Eq, Generic)

data VoteLog = MkVoteLog
  { creatorId :: PartyId
  , blockHash :: Hash Block
  }
  deriving stock (Show, Eq, Generic)
  deriving anyclass (FromJSON, ToJSON)

fromVote :: Vote -> VoteLog
fromVote MkVote{creatorId = cid, blockHash = h} = MkVoteLog{creatorId = cid, blockHash = h}

instance ToJSON PerasLog where
  toJSON = \case
    Tick s r -> A.object ["tag" .= ("Tick" :: Text), "slot" .= s, "round" .= r]
    NewChainAndVotes cs vs -> object ["tag" .= ("NewChainAndVotes" :: Text), "chains" .= (head <$> toList cs), "votes" .= fmap fromVote (toList vs)]
    NewChainPref c -> object ["tag" .= ("NewChainPref" :: Text), "chain" .= head c]
    NewCertificatesReceived cs -> object ["tag" .= ("NewCertificatesReceived" :: Text), "certificates" .= cs]
    NewCertificatesFromQuorum qs -> object ["tag" .= ("NewCertificatesFromQuorum" :: Text), "quorums" .= qs]
    NewCertPrime c -> object ["tag" .= ("NewCertPrime" :: Text), "certificate" .= c]
    NewCertStar c -> object ["tag" .= ("NewCertStar" :: Text), "certificate" .= c]
    CastVote v -> object ["tag" .= ("CastVote" :: Text), "vote" .= v]

perasTracer :: Tracer IO PerasLog
perasTracer = contramap (LT.unpack . LE.decodeUtf8 . A.encode) stdoutTracer
