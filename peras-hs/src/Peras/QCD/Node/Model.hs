{-# LANGUAGE DeriveGeneric #-}

module Peras.QCD.Node.Model where

import Numeric.Natural (Natural)
import Peras.QCD.Crypto (ByteString, Hash (MakeHash), Hashable (hash), emptyBS)
import Peras.QCD.State (Lens', State, lens', use, (≔), (≕))
import Peras.QCD.Util (addOne, count, eqBy, eqByBS, firstWithDefault, groupBy, unionDescending, (⇉))

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

chainBlocks :: Chain -> [Block]
chainBlocks Genesis = []
chainBlocks (ChainBlock block chain) = block : chainBlocks chain

genesisCert :: Certificate
genesisCert = MakeCertificate 0 genesisHash

certsOnChain :: Chain -> [Certificate]
certsOnChain Genesis = [genesisCert]
certsOnChain (ChainBlock block chain) =
  maybe id (:) (certificate block) $ certsOnChain chain

lastCert :: Chain -> Certificate
lastCert Genesis = genesisCert
lastCert (ChainBlock block chain) =
  maybe (lastCert chain) id (certificate block)

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

buildCertificate :: [Vote] -> Certificate
buildCertificate votes' =
  MakeCertificate (getRound votes') (getBlock votes')
 where
  getRound :: [Vote] -> Round
  getRound [] = zero
  getRound (vote : _) = voteRound vote
  getBlock :: [Vote] -> Hash Block
  getBlock [] = genesisHash
  getBlock (vote : _) = voteBlock vote

initialize :: Params -> PartyId -> NodeOperation
initialize params party =
  do
    protocol ≔ params
    creatorId ≔ party
    diffuse

isChainPrefix :: Chain -> Chain -> Bool
isChainPrefix Genesis _ = True
isChainPrefix (ChainBlock block _) chain' =
  test (chainBlocks chain')
 where
  sl :: Slot
  sl = slot block
  hb :: Hash Block
  hb = hash block
  test :: [Block] -> Bool
  test [] = False
  test (b : bs) = hb == parent b || sl < slot b && test bs

updateChains :: [Chain] -> NodeModification
updateChains newChains =
  do
    certs ≕ insertCerts (concatMap certsOnChain newChains)
    chains ≕ filter (not . isPrefixOfAnyChain newChains)
    isPrefixOfOldChains <- use chains ⇉ isPrefixOfAnyChain
    chains ≕ mappend (filter (not . isPrefixOfOldChains) newChains)
 where
  insertCerts :: [Certificate] -> [Certificate] -> [Certificate]
  insertCerts = unionDescending (\r -> certificateRound r)
  isPrefixOfAnyChain :: [Chain] -> Chain -> Bool
  isPrefixOfAnyChain chains' chain =
    any (isChainPrefix chain) chains'

chainWeight :: Natural -> [Certificate] -> Chain -> Natural
chainWeight boost certs' chain =
  count (chainBlocks chain ⇉ hash)
    + boost
      * count
        ( filter
            (flip elem (certs' ⇉ \r -> certificateBlock r))
            (chainBlocks chain ⇉ hash)
        )

heaviestChain :: Natural -> [Certificate] -> [Chain] -> Chain
heaviestChain _ _ [] = Genesis
heaviestChain boost certs' (chain : chains') =
  heaviest (chain, chainWeight boost certs' chain) chains'
 where
  heaviest :: (Chain, Natural) -> [Chain] -> Chain
  heaviest (c, _) [] = c
  heaviest (c, w) (c' : cs) =
    if w <= chainWeight boost certs' c'
      then heaviest (c', chainWeight boost certs' c') cs
      else heaviest (c, w) cs

certificatesForNewQuorums :: State NodeModel [Certificate]
certificatesForNewQuorums =
  do
    tau <- peras τ
    roundsWithCerts <- use certs ⇉ fmap (\r -> certificateRound r)
    ( ( (use votes ⇉ filter (hasNoCertificate roundsWithCerts))
          ⇉ groupByRound
      )
        ⇉ filter (hasQuorum tau)
      )
      ⇉ fmap buildCertificate
 where
  hasNoCertificate :: [Round] -> Vote -> Bool
  hasNoCertificate roundsWithCerts vote =
    notElem (voteRound vote) roundsWithCerts
  groupByRound :: [Vote] -> [[Vote]]
  groupByRound = groupBy (eqBy (\r -> voteRound r))
  hasQuorum :: Natural -> [a] -> Bool
  hasQuorum tau votes' = count votes' >= tau

updateLatestCertSeen :: NodeModification
updateLatestCertSeen =
  (use certs ⇉ firstWithDefault genesisCert) >>= (latestCertSeen ≔)

updateLatestCertOnChain :: NodeModification
updateLatestCertOnChain =
  (use preferredChain ⇉ lastCert) >>= (latestCertOnChain ≔)

fetching :: [Chain] -> [Vote] -> NodeOperation
fetching newChains newVotes =
  do
    currentSlot ≕ addOne
    updateChains newChains
    votes ≕ insertVotes newVotes
    newCerts <- certificatesForNewQuorums
    certs ≕ insertCerts newCerts
    boost <- peras B
    heaviest <- heaviestChain boost <$> use certs <*> use chains
    preferredChain ≔ heaviest
    updateLatestCertSeen
    updateLatestCertOnChain
    diffuse
 where
  insertVotes :: [Vote] -> [Vote] -> [Vote]
  insertVotes = unionDescending (\r -> voteRound r)
  insertCerts :: [Certificate] -> [Certificate] -> [Certificate]
  insertCerts = unionDescending (\r -> certificateRound r)
