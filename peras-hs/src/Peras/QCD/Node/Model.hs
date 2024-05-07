{-# LANGUAGE DeriveGeneric #-}

module Peras.QCD.Node.Model where

import Numeric.Natural (Natural)
import Peras.QCD.State (Lens', State, lens', use, (≔), (≕))

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS (empty)
import Data.Default (Default (..))
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import Peras.Orphans ()

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

eqOn :: Eq b => (a -> b) -> a -> a -> Bool
eqOn f x y = f x == f y

emptyBS :: ByteString
emptyBS = BS.empty
eqBS :: ByteString -> ByteString -> Bool
eqBS = (==)

newtype Hash a = Hash {hashBytes :: ByteString}
  deriving (Generic, Show)

instance Eq (Hash a) where
  (==) = eqOn (\r -> hashBytes r)

class Hashable a where
  hash :: a -> Hash a

newtype MembershipProof = MembershipProof
  { membershipProofBytes ::
      ByteString
  }
  deriving (Generic, Show)

instance Eq MembershipProof where
  (==) = eqOn (\r -> membershipProofBytes r)

newtype LeadershipProof = LeadershipProof
  { leadershipProofBytes ::
      ByteString
  }
  deriving (Generic, Show)

instance Eq LeadershipProof where
  (==) = eqOn (\r -> leadershipProofBytes r)

newtype Signature = Signature {signatureBytes :: ByteString}
  deriving (Generic, Show)

instance Eq Signature where
  (==) = eqOn (\r -> signatureBytes r)

newtype VerificationKey = VerificationKey
  { verificationKeyBytes ::
      ByteString
  }
  deriving (Generic, Show)

instance Eq VerificationKey where
  (==) = eqOn (\r -> verificationKeyBytes r)

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
genesisHash = Hash emptyBS

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

duplicateVote :: Vote -> Vote -> Bool
duplicateVote x y =
  eqOn (\r -> voteRound r) x y && eqOn (\r -> voteParty r) x y

equivocatedVote :: Vote -> Vote -> Bool
equivocatedVote x y =
  eqOn (\r -> voteRound r) x y
    && eqOn (\r -> voteParty r) x y
    && not (eqOn (\r -> voteBlock r) x y)

data Message
  = NewChain Chain
  | NewVote Vote
  | NewCertificate Certificate
  deriving (Generic, Show)

instance Eq Vote where
  x == y =
    eqOn (\r -> voteRound r) x y
      && eqOn (\r -> voteParty r) x y
      && eqOn (\r -> voteBlock r) x y
      && eqOn (\r -> voteProof r) x y
      && eqOn (\r -> voteSignature r) x y

instance Eq Certificate where
  x == y =
    eqOn (\r -> certificateRound r) x y
      && eqOn (\r -> certificateBlock r) x y

instance Eq Block where
  x == y =
    eqOn (\r -> slot r) x y
      && eqOn (\r -> creator r) x y
      && eqOn (\r -> parent r) x y
      && eqOn (\r -> certificate r) x y
      && eqOn (\r -> leadershipProof r) x y
      && eqOn (\r -> bodyHash r) x y

instance Hashable Block where
  hash = \b -> Hash (signatureBytes (signature b))

instance Eq BlockBody where
  x == y =
    eqOn (\r -> headerHash r) x y && eqOn (\r -> payload r) x y

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

type SignBlock =
  Slot -> PartyId -> Hash Block -> Maybe Certificate -> Block

type SignVote = Round -> PartyId -> Hash Block -> Vote

incrementSlot :: Slot -> Slot
incrementSlot s = s + 1

incrementRound :: Round -> Round
incrementRound r = r + 1

checkDescending :: (a -> a -> Ordering) -> [a] -> Bool
checkDescending _ [] = True
checkDescending _ [x] = True
checkDescending f (x : (y : zs)) =
  f x y == GT && checkDescending f (y : zs)

insertDescending :: (a -> a -> Ordering) -> a -> [a] -> [a]
insertDescending _ x [] = [x]
insertDescending f x (y : ys) =
  case f x y of
    LT -> y : insertDescending f x ys
    EQ -> y : ys
    GT -> x : (y : ys)

unionDescending :: Ord b => (a -> b) -> [a] -> [a] -> [a]
unionDescending f xs ys =
  foldr (insertDescending (\x y -> compare (f x) (f y))) ys xs

groupBy :: (a -> a -> Bool) -> [a] -> [[a]]
groupBy _ [] = []
groupBy f (x : xs) =
  (x : fst (span (f x) xs)) : groupBy f (snd (span (f x) xs))

count :: [a] -> Natural
count _ = 0

diffuse :: NodeOperation
diffuse = pure []

(↞) :: Applicative f => f [a] -> a -> f [a]
m ↞ x = fmap (\xs -> xs ++ [x]) m

infixl 5 ↞

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
    roundsWithCerts <- fmap (\r -> certificateRound r) <$> use certs
    fmap
      ( \votes ->
          case votes of
            [] -> zero
            vote : _ -> voteRound vote
      )
      . filter (\votes -> count votes >= tau)
      . (groupBy $ eqOn (\r -> voteRound r))
      . filter (\vote -> notElem (voteRound vote) roundsWithCerts)
      <$> use votes

updateVotes :: [Vote] -> NodeModification
updateVotes newVotes =
  do
    votes ≕ unionDescending (\r -> voteRound r) newVotes
    rs <- roundsWithNewQuorums
    pure ()

fetching :: [Chain] -> [Vote] -> NodeOperation
fetching newChains newVotes =
  do
    currentSlot ≕ incrementSlot
    updateChains newChains
    updateVotes newVotes
    diffuse
