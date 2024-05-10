{-# LANGUAGE DeriveGeneric #-}

module Peras.QCD.Node.Model where

import Numeric.Natural (Natural)
import Peras.QCD.Crypto (emptyBS)
import Peras.QCD.Protocol (ParamSymbol, Params, defaultParams, perasParam)
import Peras.QCD.State (Lens', State, lens', use)
import Peras.QCD.Types (Certificate, Chain, Message, PartyId, Round, Slot, VerificationKey (MakeVerificationKey), Vote, genesisCert)

import Data.Default (Default (..))
import GHC.Generics (Generic)
import Peras.QCD.Types.Instances ()

data NodeModel = NodeModel
  { nodeProtocol :: Params
  , nodeCreatorId :: PartyId
  , nodeCurrentSlot :: Slot
  , nodeCurrentRound :: Round
  , nodePreferredChain :: Chain
  , nodeChains :: [Chain]
  , nodeVotes :: [Vote]
  , nodeCerts :: [Certificate]
  , nodeLatestCertSeen :: Certificate
  , nodeLatestCertOnChain :: Certificate
  }
  deriving (Generic, Show)

emptyNode :: NodeModel
emptyNode =
  NodeModel
    defaultParams
    (MakeVerificationKey emptyBS)
    0
    0
    []
    [[]]
    []
    [genesisCert]
    genesisCert
    genesisCert

instance Default NodeModel where
  def = emptyNode

protocol :: Lens' NodeModel Params
protocol =
  lens'
    (\r -> nodeProtocol r)
    ( \s x ->
        NodeModel
          x
          (nodeCreatorId s)
          (nodeCurrentSlot s)
          (nodeCurrentRound s)
          (nodePreferredChain s)
          (nodeChains s)
          (nodeVotes s)
          (nodeCerts s)
          (nodeLatestCertSeen s)
          (nodeLatestCertOnChain s)
    )

peras :: ParamSymbol -> State NodeModel Natural
peras x = perasParam x <$> use protocol

creatorId :: Lens' NodeModel PartyId
creatorId =
  lens'
    (\r -> nodeCreatorId r)
    ( \s x ->
        NodeModel
          (nodeProtocol s)
          x
          (nodeCurrentSlot s)
          (nodeCurrentRound s)
          (nodePreferredChain s)
          (nodeChains s)
          (nodeVotes s)
          (nodeCerts s)
          (nodeLatestCertSeen s)
          (nodeLatestCertOnChain s)
    )

currentSlot :: Lens' NodeModel Slot
currentSlot =
  lens'
    (\r -> nodeCurrentSlot r)
    ( \s x ->
        NodeModel
          (nodeProtocol s)
          (nodeCreatorId s)
          x
          (nodeCurrentRound s)
          (nodePreferredChain s)
          (nodeChains s)
          (nodeVotes s)
          (nodeCerts s)
          (nodeLatestCertSeen s)
          (nodeLatestCertOnChain s)
    )

currentRound :: Lens' NodeModel Round
currentRound =
  lens'
    (\r -> nodeCurrentRound r)
    ( \s x ->
        NodeModel
          (nodeProtocol s)
          (nodeCreatorId s)
          (nodeCurrentSlot s)
          x
          (nodePreferredChain s)
          (nodeChains s)
          (nodeVotes s)
          (nodeCerts s)
          (nodeLatestCertSeen s)
          (nodeLatestCertOnChain s)
    )

preferredChain :: Lens' NodeModel Chain
preferredChain =
  lens'
    (\r -> nodePreferredChain r)
    ( \s x ->
        NodeModel
          (nodeProtocol s)
          (nodeCreatorId s)
          (nodeCurrentSlot s)
          (nodeCurrentRound s)
          x
          (nodeChains s)
          (nodeVotes s)
          (nodeCerts s)
          (nodeLatestCertSeen s)
          (nodeLatestCertOnChain s)
    )

chains :: Lens' NodeModel [Chain]
chains =
  lens'
    (\r -> nodeChains r)
    ( \s x ->
        NodeModel
          (nodeProtocol s)
          (nodeCreatorId s)
          (nodeCurrentSlot s)
          (nodeCurrentRound s)
          (nodePreferredChain s)
          x
          (nodeVotes s)
          (nodeCerts s)
          (nodeLatestCertSeen s)
          (nodeLatestCertOnChain s)
    )

votes :: Lens' NodeModel [Vote]
votes =
  lens'
    (\r -> nodeVotes r)
    ( \s x ->
        NodeModel
          (nodeProtocol s)
          (nodeCreatorId s)
          (nodeCurrentSlot s)
          (nodeCurrentRound s)
          (nodePreferredChain s)
          (nodeChains s)
          x
          (nodeCerts s)
          (nodeLatestCertSeen s)
          (nodeLatestCertOnChain s)
    )

certs :: Lens' NodeModel [Certificate]
certs =
  lens'
    (\r -> nodeCerts r)
    ( \s x ->
        NodeModel
          (nodeProtocol s)
          (nodeCreatorId s)
          (nodeCurrentSlot s)
          (nodeCurrentRound s)
          (nodePreferredChain s)
          (nodeChains s)
          (nodeVotes s)
          x
          (nodeLatestCertSeen s)
          (nodeLatestCertOnChain s)
    )

latestCertSeen :: Lens' NodeModel Certificate
latestCertSeen =
  lens'
    (\r -> nodeLatestCertSeen r)
    ( \s x ->
        NodeModel
          (nodeProtocol s)
          (nodeCreatorId s)
          (nodeCurrentSlot s)
          (nodeCurrentRound s)
          (nodePreferredChain s)
          (nodeChains s)
          (nodeVotes s)
          (nodeCerts s)
          x
          (nodeLatestCertOnChain s)
    )

latestCertOnChain :: Lens' NodeModel Certificate
latestCertOnChain =
  lens'
    (\r -> nodeLatestCertOnChain r)
    ( \s x ->
        NodeModel
          (nodeProtocol s)
          (nodeCreatorId s)
          (nodeCurrentSlot s)
          (nodeCurrentRound s)
          (nodePreferredChain s)
          (nodeChains s)
          (nodeVotes s)
          (nodeCerts s)
          (nodeLatestCertSeen s)
          x
    )

type NodeState s = State NodeModel s

type NodeOperation = NodeState [Message]

type NodeModification = NodeState ()

diffuse :: NodeOperation
diffuse = pure []
