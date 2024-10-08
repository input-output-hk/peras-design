{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Peras.Prototype.Trace where

import Control.Tracer (Tracer (..), contramap, debugTracer)
import Data.Aeson (FromJSON, ToJSON)
import qualified Data.Aeson as A
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.Encoding as LE
import GHC.Generics (Generic)
import Peras.Block (Block, Certificate, PartyId)
import Peras.Chain (Chain, Vote (..))
import Peras.Crypto (Hash)
import Peras.Numbering (RoundNumber, SlotNumber)
import Peras.Orphans ()
import Peras.Prototype.Types (PerasParams, PerasState, VotingWeight)

data PerasLog
  = Protocol {parameters :: PerasParams}
  | Tick {slot :: SlotNumber, roundNumber :: RoundNumber}
  | NewChainAndVotes {partyId :: PartyId, newChains :: [Chain], newVotes :: [Vote]}
  | NewChainPref {partyId :: PartyId, newChainPref :: Chain}
  | NewCertificatesReceived {partyId :: PartyId, newCertificates :: [(Certificate, SlotNumber)]}
  | NewCertificatesFromQuorum {partyId :: PartyId, newQuorums :: [Certificate]}
  | NewCertPrime {partyId :: PartyId, newCertPrime :: Certificate}
  | NewCertStar {partyId :: PartyId, newCertStar :: Certificate}
  | CastVote {partyId :: PartyId, vote :: Vote}
  | SelectedBlock {partyId :: PartyId, block :: Block, weight :: VotingWeight}
  | NoBlockSelected {partyId :: PartyId}
  | ForgingLogic {partyId :: PartyId, bc1a :: Bool, bc1b :: Bool, bc1c :: Bool, block :: Block}
  | VotingLogic {partyId :: PartyId, vr1a :: Bool, vr1b :: Bool, vr2a :: Bool, vr2b :: Bool}
  | DiffuseChain {partyId :: PartyId, chain :: Chain}
  | DiffuseVote {partyId :: PartyId, vote :: Vote}
  | Snapshot {state :: PerasState}
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
perasTracer = contramap (LT.unpack . LE.decodeUtf8 . A.encode) debugTracer
