{-# LANGUAGE DeriveGeneric #-}

module Peras.QCD.Node.Model where

import Numeric.Natural (Natural)
import Peras.Block (Block (slotNumber), Certificate (votingRoundNumber), PartyId, Slot)
import Peras.Chain (Chain, RoundNumber (MkRoundNumber, roundNumber), Vote (votingRound))
import Peras.Crypto (Hash)
import Peras.Message (Message (NewChain, SomeVote))
import Peras.QCD.State (Lens', State, lens', use, (≔), (≕))

import Data.Default (Default (..))
import GHC.Generics (Generic)
import Peras.Orphans ()

data Params = Params
  { paramU :: Natural
  , paramL :: Natural
  , paramA :: Natural
  }
  deriving (Eq, Generic, Ord, Show)

defaultParams :: Params
defaultParams = Params 120 10 240

instance Default Params where
  def = defaultParams

type HashBlock = Block -> Hash Block

type HashTip = Chain -> Hash Block

type SignBlock =
  Slot -> PartyId -> Hash Block -> Maybe Certificate -> Block

type SignVote = RoundNumber -> PartyId -> Hash Block -> Vote

data CryptoFunctions = CryptoFunctions
  { hashBlockFunction ::
      HashBlock
  , hashTipFunction :: HashTip
  , signBlockFunction :: SignBlock
  , signVoteFunction :: SignVote
  }

data NodeModel = NodeModel
  { nodeProtocol :: Params
  , nodeCreatorId :: PartyId
  , nodeCurrentSlot :: Slot
  , nodeCurrentRound :: RoundNumber
  , nodePreferredChain :: Chain
  , nodePreferredCerts :: [Certificate]
  , nodePreferredVotes :: [Vote]
  }
  deriving (Eq, Generic, Ord, Show)

emptyNode :: NodeModel
emptyNode = NodeModel defaultParams 0 0 (MkRoundNumber 0) [] [] []

instance Default NodeModel where
  def = emptyNode

type NodeOperation = State NodeModel [Message]

type NodeModification = State NodeModel ()

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
          (nodePreferredCerts s)
          (nodePreferredVotes s)
    )

peras :: (Params -> a) -> State NodeModel a
peras x = x <$> use protocol

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
          (nodePreferredCerts s)
          (nodePreferredVotes s)
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
          (nodePreferredCerts s)
          (nodePreferredVotes s)
    )

currentRound :: Lens' NodeModel RoundNumber
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
          (nodePreferredCerts s)
          (nodePreferredVotes s)
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
          (nodePreferredCerts s)
          (nodePreferredVotes s)
    )

preferredCerts :: Lens' NodeModel [Certificate]
preferredCerts =
  lens'
    (\r -> nodePreferredCerts r)
    ( \s x ->
        NodeModel
          (nodeProtocol s)
          (nodeCreatorId s)
          (nodeCurrentSlot s)
          (nodeCurrentRound s)
          (nodePreferredChain s)
          x
          (nodePreferredVotes s)
    )

preferredVotes :: Lens' NodeModel [Vote]
preferredVotes =
  lens'
    (\r -> nodePreferredVotes r)
    ( \s x ->
        NodeModel
          (nodeProtocol s)
          (nodeCreatorId s)
          (nodeCurrentSlot s)
          (nodeCurrentRound s)
          (nodePreferredChain s)
          (nodePreferredCerts s)
          x
    )

incrementSlot :: Slot -> Slot
incrementSlot s = s + 1

incrementRound :: RoundNumber -> RoundNumber
incrementRound (MkRoundNumber r) = MkRoundNumber (r + 1)

messages :: NodeOperation
messages = pure []

(↞) :: Applicative f => f [a] -> a -> f [a]
m ↞ x = fmap (\xs -> xs ++ [x]) m

infixl 5 ↞

initialize :: Params -> PartyId -> NodeOperation
initialize params party =
  do
    protocol ≔ params
    creatorId ≔ party
    messages

discardExpiredCerts :: NodeModification
discardExpiredCerts =
  do
    now <- use currentSlot
    u <- peras (\r -> paramU r)
    a <- peras (\r -> paramA r)
    preferredCerts
      ≕ filter (not . \cert -> u * votingRoundNumber cert + a < now)

discardExpiredVotes :: NodeModification
discardExpiredVotes =
  do
    now <- use currentSlot
    u <- peras (\r -> paramU r)
    a <- peras (\r -> paramA r)
    preferredVotes
      ≕ filter
        (not . \vote -> u * roundNumber (votingRound vote) + a < now)

newSlot :: NodeOperation
newSlot =
  do
    currentSlot ≕ incrementSlot
    discardExpiredCerts
    discardExpiredVotes
    messages

newRound :: NodeOperation
newRound =
  do
    currentRound ≕ incrementRound
    messages

forgeBlock :: HashTip -> SignBlock -> NodeOperation
forgeBlock hashTip signBlock =
  do
    chain <- use preferredChain
    parentHash <- pure $ hashTip chain
    cert <- pure Nothing
    block <-
      signBlock
        <$> use currentSlot
        <*> use creatorId
        <*> pure parentHash
        <*> pure cert
    chain' <- pure $ (block : chain)
    preferredChain ≔ chain'
    messages ↞ NewChain chain'

buildCert :: NodeModel -> [Message] -> (NodeModel, [Message])
buildCert node messages' = (node, messages')

castVote ::
  NodeModel -> HashBlock -> SignVote -> (NodeModel, [Message])
castVote node hashBlock signVote =
  buildCert
    ( NodeModel
        (nodeProtocol node)
        (nodeCreatorId node)
        (nodeCurrentSlot node)
        (nodeCurrentRound node)
        (nodePreferredChain node)
        (nodePreferredCerts node)
        (nodePreferredVotes node ++ vote)
    )
    (map SomeVote vote)
 where
  eligible :: Block -> Bool
  eligible block =
    slotNumber block + paramL (nodeProtocol node)
      <= nodeCurrentSlot node
  vote :: [Vote]
  vote =
    case filter eligible (nodePreferredChain node) of
      [] -> []
      block : _ ->
        [ signVote
            (nodeCurrentRound node)
            (nodeCreatorId node)
            (hashBlock block)
        ]

test1 :: State NodeModel Slot
test1 =
  do
    i <- use currentSlot
    currentSlot ≔ (i + 1)
    currentSlot ≕ \j -> j + 10
    use currentSlot

data Signal
  = Initialize Params PartyId
  | NewSlot
  | NewRound
  | ForgeBlock
  | CastVote
  | ReceiveBlock Block
  | ReceiveVote Vote
  | ReceiveCertificate Certificate
  deriving (Eq, Generic, Ord, Show)
