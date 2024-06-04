{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Peras.Abstract.Protocol.Trace where

import Control.Tracer (Tracer (..), contramap, stdoutTracer)
import Data.Aeson (FromJSON, ToJSON)
import qualified Data.Aeson as A
import Data.Set (Set)
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
  | NewChainAndVotes {partyId :: PartyId, newChains :: Set Chain, newVotes :: Set Vote}
  | NewChainPref {partyId :: PartyId, newChainPref :: Chain}
  | NewCertificatesReceived {partyId :: PartyId, newCertificates :: [(Certificate, SlotNumber)]}
  | NewCertificatesFromQuorum {partyId :: PartyId, newQuorums :: [Certificate]}
  | NewCertPrime {partyId :: PartyId, newCertPrime :: Certificate}
  | NewCertStar {partyId :: PartyId, newCertStar :: Certificate}
  | CastVote {partyId :: PartyId, vote :: Vote}
  | PreagreementBlock {partyId :: PartyId, block :: Block, weight :: VotingWeight}
  | PreagreementNone {partyId :: PartyId}
  | ForgingLogic {partyId :: PartyId, bc1a :: Bool, bc1b :: Bool, bc1c :: Bool}
  | VotingLogic {partyId :: PartyId, vr1a :: Bool, vr1b :: Bool, vr2a :: Bool, vr2b :: Bool}
  | DiffuseChain {partyId :: PartyId, chain :: Chain}
  | DiffuseVote {partyId :: PartyId, vote :: Vote}
  deriving stock (Show, Eq, Generic)

data VoteLog = MkVoteLog
  { creatorId :: PartyId
  , blockHash :: Hash Block
  }
  deriving stock (Show, Eq, Generic)

instance FromJSON VoteLog
instance ToJSON VoteLog

fromVote :: Vote -> VoteLog
fromVote MkVote{creatorId = cid, blockHash = h} = MkVoteLog{creatorId = cid, blockHash = h}

instance FromJSON PerasLog
instance ToJSON PerasLog

perasTracer :: Tracer IO PerasLog
perasTracer = contramap (LT.unpack . LE.decodeUtf8 . A.encode) stdoutTracer
