{-# LANGUAGE DeriveGeneric #-}

module Peras.QCD.Node.Model where

import Numeric.Natural (Natural)
import Peras.QCD.Crypto (ByteString, Hash (MakeHash), Hashable (hash), emptyBS)
import Peras.QCD.State (Lens', State, lens', use, (≔), (≕))
import Peras.QCD.Util (addOne, count, eqBy, eqByBS, groupBy, unionDescending, (⇉))

import Data.Default (Default (..))
import GHC.Generics (Generic)

zero :: Natural
zero = 0

data ParamSymbol
  = U
  | A
  | W
  | L
  | B
  | Τ
  | R
  | K

τ :: ParamSymbol
τ = Τ

data Params = Params
  { paramU :: Natural
  , paramA :: Natural
  , paramW :: Natural
  , paramL :: Natural
  , paramB :: Natural
  , paramΤ :: Natural
  , paramR :: Natural
  , paramK :: Natural
  }
  deriving (Eq, Generic, Ord, Show)

defaultParams :: Params
defaultParams = Params 120 240 3600 120 10 300 120 600

instance Default Params where
  def = defaultParams

perasParam :: ParamSymbol -> Params -> Natural
perasParam U = \r -> paramU r
perasParam A = \r -> paramA r
perasParam W = \r -> paramW r
perasParam L = \r -> paramL r
perasParam B = \r -> paramB r
perasParam Τ = \r -> paramΤ r
perasParam R = \r -> paramR r
perasParam K = \r -> paramK r

newtype MembershipProof = MembershipProof
  { membershipProofBytes ::
      ByteString
  }
  deriving (Generic, Show)

newtype LeadershipProof = LeadershipProof
  { leadershipProofBytes ::
      ByteString
  }
  deriving (Generic, Show)

newtype Signature = Signature {signatureBytes :: ByteString}
  deriving (Generic, Show)

newtype VerificationKey = VerificationKey
  { verificationKeyBytes ::
      ByteString
  }
  deriving (Generic, Show)

type Slot = Natural

type Round = Natural

type PartyId = VerificationKey

data Certificate = MakeCertificate
  { certificateRound :: Round
  , certificateBlock :: Hash Block
  }
  deriving (Generic, Show)

type Tx = ()

data Block = MakeBlock
  { slot :: Slot
  , creator :: PartyId
  , parent :: Hash Block
  , certificate :: Maybe Certificate
  , leadershipProof :: LeadershipProof
  , signature :: Signature
  , bodyHash :: Hash [Tx]
  }
  deriving (Generic, Show)

data BlockBody = BlockBody
  { headerHash :: Hash Block
  , payload :: [Tx]
  }
  deriving (Generic, Show)

data Chain
  = Genesis
  | ChainBlock Block Chain
  deriving (Generic, Show)

genesisHash :: Hash Block
genesisHash = MakeHash emptyBS

genesisCert :: Certificate
genesisCert = MakeCertificate 0 genesisHash

data Vote = Vote
  { voteRound :: Natural
  , voteParty :: PartyId
  , voteBlock :: Hash Block
  , voteProof :: MembershipProof
  , voteSignature :: Signature
  }
  deriving (Generic, Show)

data Message
  = NewChain Chain
  | NewVote Vote
  | NewCertificate Certificate
  deriving (Generic, Show)

instance Eq MembershipProof where
  (==) = eqByBS (\r -> membershipProofBytes r)

instance Eq LeadershipProof where
  (==) = eqByBS (\r -> leadershipProofBytes r)

instance Eq Signature where
  (==) = eqByBS (\r -> signatureBytes r)

instance Eq VerificationKey where
  (==) = eqByBS (\r -> verificationKeyBytes r)

instance Eq Vote where
  x == y =
    eqBy (\r -> voteRound r) x y
      && eqBy (\r -> voteParty r) x y
      && eqBy (\r -> voteBlock r) x y
      && eqBy (\r -> voteProof r) x y
      && eqBy (\r -> voteSignature r) x y

instance Eq Certificate where
  x == y =
    eqBy (\r -> certificateRound r) x y
      && eqBy (\r -> certificateBlock r) x y

instance Eq Block where
  x == y =
    eqBy (\r -> slot r) x y
      && eqBy (\r -> creator r) x y
      && eqBy (\r -> parent r) x y
      && eqBy (\r -> certificate r) x y
      && eqBy (\r -> leadershipProof r) x y
      && eqBy (\r -> bodyHash r) x y

instance Hashable Block where
  hash = \b -> MakeHash (signatureBytes (signature b))

instance Eq BlockBody where
  x == y =
    eqBy (\r -> headerHash r) x y && eqBy (\r -> payload r) x y

instance Eq Chain where
  Genesis == Genesis = True
  ChainBlock b c == ChainBlock b' c' = b == b' && c == c'
  _ == _ = False

tipHash :: Chain -> Hash Block
tipHash Genesis = genesisHash
tipHash (ChainBlock block _) = hash block

instance Eq Message where
  NewChain x == NewChain y = x == y
  NewVote x == NewVote y = x == y
  NewCertificate x == NewCertificate y = x == y
  _ == _ = False

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
    (VerificationKey emptyBS)
    0
    0
    Genesis
    [Genesis]
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

type SignBlock =
  Slot -> PartyId -> Hash Block -> Maybe Certificate -> Block

type SignVote = Round -> PartyId -> Hash Block -> Vote

initialize :: Params -> PartyId -> NodeOperation
initialize params party =
  do
    protocol ≔ params
    creatorId ≔ party
    diffuse

updateChains :: [Chain] -> NodeModification
updateChains newChains = pure ()

roundsWithNewQuorums :: State NodeModel [Round]
roundsWithNewQuorums =
  do
    tau <- peras τ
    roundsWithCerts <- use certs ⇉ fmap (\r -> certificateRound r)
    ( ( (use votes ⇉ filter (hasNoCertificate roundsWithCerts))
          ⇉ groupByRound
      )
        ⇉ filter (hasQuorum tau)
      )
      ⇉ fmap getRound
 where
  hasNoCertificate :: [Round] -> Vote -> Bool
  hasNoCertificate ignoreRounds vote =
    notElem (voteRound vote) ignoreRounds
  groupByRound :: [Vote] -> [[Vote]]
  groupByRound = groupBy (eqBy (\r -> voteRound r))
  hasQuorum :: Natural -> [a] -> Bool
  hasQuorum tau votes' = count votes' >= tau
  getRound :: [Vote] -> Round
  getRound [] = zero
  getRound (vote : _) = voteRound vote

fetching :: [Chain] -> [Vote] -> NodeOperation
fetching newChains newVotes =
  do
    currentSlot ≕ addOne
    updateChains newChains
    votes ≕ insertVotes newVotes
    diffuse
 where
  insertVotes :: [Vote] -> [Vote] -> [Vote]
  insertVotes = unionDescending (\r -> voteRound r)
