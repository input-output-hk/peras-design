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
import Peras.Abstract.Protocol.Types (PerasParams, VotingWeight)
import Peras.Block (Block, Certificate, PartyId)
import Peras.Chain (Chain, Vote (..))
import Peras.Crypto (Hash)
import Peras.Numbering (RoundNumber, SlotNumber)
import Peras.Orphans ()

data PerasLog
  = Protocol {parameters :: PerasParams}
  | Tick {slot :: SlotNumber, roundNumber :: RoundNumber}
  | NewChainAndVotes {party :: PartyId, newChains :: Set Chain, newVotes :: Set Vote}
  | NewChainPref {party :: PartyId, newChainPref :: Chain}
  | NewCertificatesReceived {party :: PartyId, newCertificates :: [(Certificate, SlotNumber)]}
  | NewCertificatesFromQuorum {party :: PartyId, newQuorums :: [Certificate]}
  | NewCertPrime {party :: PartyId, newCertPrime :: Certificate}
  | NewCertStar {party :: PartyId, newCertStar :: Certificate}
  | CastVote {party :: PartyId, vote :: Vote}
  | PreagreementBlock {party :: PartyId, block :: Block, weight :: VotingWeight}
  | PreagreementNone {party :: PartyId}
  | ForgingLogic {party :: PartyId, bc1a :: Bool, bc1b :: Bool, bc1c :: Bool}
  | VotingLogic {party :: PartyId, vr1a :: Bool, vr1b :: Bool, vr2a :: Bool, vr2b :: Bool}
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
    Protocol p -> A.object ["tag" .= ("Protocol" :: Text), "parameters" .= p]
    Tick s r -> A.object ["tag" .= ("Tick" :: Text), "slot" .= s, "round" .= r]
    NewChainAndVotes p cs vs -> object ["tag" .= ("NewChainAndVotes" :: Text), "party" .= p, "chains" .= (head <$> toList cs), "votes" .= fmap fromVote (toList vs)]
    NewChainPref p c -> object ["tag" .= ("NewChainPref" :: Text), "party" .= p, "chain" .= head c]
    NewCertificatesReceived p cs -> object ["tag" .= ("NewCertificatesReceived" :: Text), "party" .= p, "certificates" .= cs]
    NewCertificatesFromQuorum p qs -> object ["tag" .= ("NewCertificatesFromQuorum" :: Text), "party" .= p, "quorums" .= qs]
    NewCertPrime p c -> object ["tag" .= ("NewCertPrime" :: Text), "party" .= p, "certificate" .= c]
    NewCertStar p c -> object ["tag" .= ("NewCertStar" :: Text), "party" .= p, "certificate" .= c]
    CastVote p v -> object ["tag" .= ("CastVote" :: Text), "party" .= p, "vote" .= v]
    PreagreementBlock p b w -> object ["tag" .= ("PreagreementBlock" :: Text), "party" .= p, "block" .= b, "weight" .= w]
    PreagreementNone p -> object ["tag" .= ("PreagreementNone" :: Text), "party" .= p]
    ForgingLogic p b1a b1b b1c -> object ["tag" .= ("ForgingLogic" :: Text), "party" .= p, "bc1a" .= b1a, "bc1b" .= b1b, "bc1c" .= b1c]
    VotingLogic p v1a v1b v2a v2b -> object ["tag" .= ("VotingLogic" :: Text), "party" .= p, "v1a" .= v1a, "v1b" .= v1b, "v2a" .= v2a, "v2b" .= v2b]

perasTracer :: Tracer IO PerasLog
perasTracer = contramap (LT.unpack . LE.decodeUtf8 . A.encode) stdoutTracer
