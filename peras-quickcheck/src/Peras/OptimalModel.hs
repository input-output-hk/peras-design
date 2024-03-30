{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module Peras.OptimalModel (
  -- * Idealized Peras
  BlockIdeal (..),
  CertIdeal,
  ChainIdeal,
  IsCommitteeMember,
  IsSlotLeader,
  MessageIdeal (..),
  Protocol (..),
  VoteIdeal (..),
  idealizeBlock,
  idealizeCert,
  idealizeChain,
  idealizeMessage,
  idealizeVote,
  mkBlockIdeal,
  realizeBlock,
  realizeCert,
  realizeChain,
  realizeVote,

  -- * Node model
  NodeModel (..),

  -- * Executable specification
  chainLength,
  evaluateChain,
  includeCert,
  includeVote,
  issueBlock,
  issueCert,
  issueVote,
  nextSlot,

  -- * Real interface for Peras nodes
  PerasNode (..),

  -- * Run monad
  RunMonad (..),
  ExampleNode (..),
  initialize,
) where

import Control.Arrow ((&&&))
import Control.Monad ((<=<))
import Control.Monad.State (
  MonadState (get, put),
  MonadTrans (..),
  StateT (StateT),
  evalState,
  execState,
  gets,
  modify,
 )
import Data.Default (Default (..))
import Data.Function (on)
import qualified Data.Hashable as Hashable (hash)
import Data.List (groupBy, maximumBy, sort)
import Data.Maybe (mapMaybe)
import qualified Data.Serialize as Serialize (encode)
import Numeric.Natural (Natural)
import Peras.Arbitraries ()
import Peras.Block (Block (Block), Certificate (Certificate), PartyId, Slot)
import qualified Peras.Block as Block (Block (..))
import qualified Peras.Block as Certificate (Certificate (..))
import Peras.Chain (Chain, RoundNumber (..), Vote (MkVote))
import qualified Peras.Chain as Vote (Vote (..))
import Peras.Crypto (Hash (Hash), LeadershipProof (LeadershipProof), MembershipProof (MembershipProof), Signature (Signature))
import Peras.Crypto as Signature (Signature (bytes))
import qualified Peras.Crypto as Crypto (hashBytes)
import Peras.Message (Message (..))
import Peras.Orphans ()
import Test.QuickCheck (Gen, arbitrary, elements, frequency, getNonNegative, suchThat)
import Test.QuickCheck.DynamicLogic (DynLogicModel)
import Test.QuickCheck.StateModel (Any (Some), HasVariables (..), Realized, RunModel (perform, postcondition), StateModel (..))

--------------------------------------------------------------------------------

-- Idealized types for node model

-- TODO: It might be possible to do without these idealizations, but
-- trying this out is an informative exercise. These idealizations could
-- be eliminated if all of the cryptography etc. is fully specified.

-- | Simplified Peras parameters. FIXME: Move to Agda.
data Protocol = Peras
  { roundLength :: Natural
  , quorum :: Int
  , boost :: Double
  }
  deriving (Eq, Ord, Show)

instance Default Protocol where
  def = Peras{roundLength = 1, quorum = maxBound, boost = 0}

type IsSlotLeader = Bool

type IsCommitteeMember = Bool

data VoteIdeal = VoteIdeal
  { voter :: PartyId
  , voteRound :: Natural
  , voted :: Hash Block
  }
  deriving (Eq, Ord, Show)

realizeVote :: VoteIdeal -> Vote
realizeVote VoteIdeal{voter, voteRound, voted} =
  MkVote
    { votingRound = MkRoundNumber voteRound
    , creatorId = voter
    , blockHash = voted
    , committeeMembershipProof = MembershipProof mempty
    , signature = Signature mempty
    }

idealizeVote :: Vote -> VoteIdeal
idealizeVote MkVote{creatorId, votingRound, blockHash} =
  VoteIdeal
    { voter = creatorId
    , voteRound = roundNumber votingRound
    , voted = blockHash
    }

type CertIdeal = Certificate

realizeCert :: CertIdeal -> Certificate
realizeCert = id

idealizeCert :: Certificate -> CertIdeal
idealizeCert = id

data BlockIdeal = BlockIdeal
  { hash :: Hash Block
  , creator :: PartyId
  , slot :: Slot
  , cert :: Maybe CertIdeal
  , parent :: Hash Block
  }
  deriving (Eq, Ord, Show)

mkBlockIdeal :: PartyId -> Slot -> Maybe CertIdeal -> Hash Block -> BlockIdeal
mkBlockIdeal creator slot cert parent =
  BlockIdeal
    { hash = Hash . Serialize.encode $ Hashable.hash (creator, slot, cert, parent)
    , creator
    , slot
    , cert
    , parent
    }

realizeBlock :: BlockIdeal -> Block
realizeBlock BlockIdeal{hash, creator, slot, parent, cert} =
  Block
    { slotNumber = slot
    , creatorId = creator
    , parentBlock = parent
    , certificate = realizeCert <$> cert
    , leadershipProof = LeadershipProof mempty
    , signature = Signature $ Crypto.hashBytes hash
    , bodyHash = Hash mempty
    }

idealizeBlock :: Block -> BlockIdeal
idealizeBlock Block{slotNumber, creatorId, parentBlock, certificate, signature} =
  BlockIdeal
    { hash = Hash $ Signature.bytes signature
    , slot = slotNumber
    , creator = creatorId
    , parent = parentBlock
    , cert = idealizeCert <$> certificate
    }

type ChainIdeal = [BlockIdeal]

realizeChain :: ChainIdeal -> Chain
realizeChain = fmap realizeBlock

idealizeChain :: Chain -> ChainIdeal
idealizeChain = fmap idealizeBlock

genesisHash :: Hash Block
genesisHash = Hash mempty

hashTip :: ChainIdeal -> Hash Block
hashTip [] = genesisHash
hashTip (b : _) = hash b

finalSlot :: ChainIdeal -> Slot
finalSlot [] = 0
finalSlot (b : _) = slot b

data MessageIdeal
  = NewChainIdeal ChainIdeal
  | SomeCertIdeal CertIdeal
  | SomeVoteIdeal VoteIdeal
  deriving (Eq, Ord, Show)

idealizeMessage :: Message -> Maybe MessageIdeal
idealizeMessage (NewChain chain) = pure . NewChainIdeal $ idealizeChain chain
idealizeMessage (SomeCertificate cert) = pure . SomeCertIdeal $ idealizeCert cert
idealizeMessage (SomeVote vote) = pure . SomeVoteIdeal $ idealizeVote vote
idealizeMessage _ = Nothing

--------------------------------------------------------------------------------

-- Node model, based on idealized types

data NodeModel = NodeModel
  { protocol :: Protocol
  , self :: PartyId
  , now :: Slot
  , preferredChain :: ChainIdeal
  , preferredCerts :: [CertIdeal]
  , preferredVotes :: [VoteIdeal]
  }
  deriving (Eq, Ord, Show)

instance Default NodeModel where
  def = NodeModel def 0 0 def def def

instance HasVariables NodeModel where
  getAllVariables = mempty

instance DynLogicModel NodeModel

--------------------------------------------------------------------------------

-- Executable specficiation

nextSlot :: Monad m => Protocol -> IsSlotLeader -> IsCommitteeMember -> StateT NodeModel m [MessageIdeal]
nextSlot protocol@Peras{roundLength} isSlotLeader isCommitteeMember = do
  state <- get
  stepSlot
  voteMessages <- if isCommitteeMember && now state `mod` roundLength == 0 then issueVote protocol else pure mempty
  blockMessages <- if isSlotLeader then issueBlock protocol else pure mempty
  pure $ voteMessages <> blockMessages

stepSlot :: Monad m => StateT NodeModel m ()
stepSlot = modify $ \state -> state{now = 1 + now state}

issueBlock :: Monad m => Protocol -> StateT NodeModel m [MessageIdeal]
issueBlock _ = do
  state <- get
  let (cert, certs) =
        case preferredCerts state of
          [] -> (Nothing, [])
          cert' : certs' -> (Just cert', certs')
      block =
        BlockIdeal
          { hash = Hash . Serialize.encode $ Hashable.hash (self state, now state, cert, hashTip $ preferredChain state)
          , creator = self state
          , slot = now state
          , cert = cert
          , parent = hashTip $ preferredChain state
          }
      chain = block : preferredChain state
  put $ state{preferredChain = chain, preferredCerts = certs}
  pure [NewChainIdeal chain]

issueVote :: Monad m => Protocol -> StateT NodeModel m [MessageIdeal]
issueVote protocol@Peras{roundLength} = do
  state <- get
  let vote =
        VoteIdeal
          { voter = self state
          , voteRound = now state `div` roundLength
          , voted = hashTip . drop 1 $ preferredChain state
          }
  put $ state{preferredVotes = preferredVotes state <> pure vote}
  certMessages <- issueCert protocol
  pure $ [SomeVoteIdeal vote] <> certMessages

issueCert :: Monad m => Protocol -> StateT NodeModel m [MessageIdeal]
issueCert Peras{quorum} = do
  state <- get
  -- Find the most votes for the same block in the most recent round that has a quorum.
  let maximumBy' _ [] = []
      maximumBy' f xs = maximumBy f xs
      candidates =
        maximumBy' (on compare $ \vs -> (voteRound $ head vs, length vs))
          . filter ((>= quorum) . length)
          . groupBy (on (==) $ voteRound &&& voted)
          $ preferredVotes state
  case candidates of
    vs@(VoteIdeal{voteRound, voted} : _) -> do
      let cert = Certificate{votingRoundNumber = voteRound, blockRef = voted}
      put $
        state
          { preferredCerts = preferredCerts state <> pure cert
          , preferredVotes = filter (`elem` vs) $ preferredVotes state
          }
      pure [SomeCertIdeal cert]
    [] -> pure mempty

evaluateChain :: Monad m => Protocol -> ChainIdeal -> StateT NodeModel m [MessageIdeal]
evaluateChain protocol chain = do
  state <- get
  if ((>) `on` chainLength (boost protocol)) chain (preferredChain state)
    then do
      -- FIXME: Adopting a new chain also involves adjusting the set of preferred
      -- certificates and votes.
      put $ state{preferredChain = chain}
      pure [NewChainIdeal chain]
    else pure mempty

chainLength :: Double -> ChainIdeal -> Double
chainLength boost' = sum . fmap (maybe 1 (const $ 1 + boost') . cert)

includeCert :: Monad m => CertIdeal -> StateT NodeModel m [MessageIdeal]
includeCert cert = do
  alreadySeen <- gets $ elem cert . preferredCerts
  modify $ \state -> state{preferredCerts = preferredCerts state <> pure cert}
  pure $
    if alreadySeen
      then mempty
      else [SomeCertIdeal cert]

includeVote :: Monad m => Protocol -> VoteIdeal -> StateT NodeModel m [MessageIdeal]
includeVote protocol vote = do
  alreadySeen <- gets $ elem vote . preferredVotes
  modify $ \state -> state{preferredVotes = preferredVotes state <> pure vote}
  certMessages <- issueCert protocol
  pure $
    if alreadySeen
      then certMessages
      else SomeVoteIdeal vote : certMessages

--------------------------------------------------------------------------------

-- State model

instance StateModel NodeModel where
  data Action NodeModel a where
    Initialize :: Protocol -> PartyId {- i.e., the owner of the node -} -> Action NodeModel ()
    ATick :: IsSlotLeader -> IsCommitteeMember -> Action NodeModel [MessageIdeal]
    ANewChain :: ChainIdeal -> Action NodeModel [MessageIdeal]
    ASomeCert :: CertIdeal -> Action NodeModel [MessageIdeal]
    ASomeVote :: VoteIdeal -> Action NodeModel [MessageIdeal]

  arbitraryAction _context NodeModel{protocol = Peras{roundLength}, self, now, preferredChain} =
    frequency
      [ (9, fmap Some . ATick <$> genSlotLeader <*> genCommitteeMember)
      , (5, Some . ANewChain <$> genChain now preferredChain)
      , (1, Some . ASomeCert <$> genCert now preferredChain)
      , (2, Some . ASomeVote <$> genVote now preferredChain)
      ]
   where
    -- FIXME: All of these generators need review and refinement.
    -- Generate slot leadership.
    genSlotLeader = frequency [(9, pure False), (1, pure True)]
    -- Generate committee membership.
    genCommitteeMember = frequency [(4, pure False), (1, pure True)]
    -- Generate a chain at a specified time and potentially building on a previous chain.
    genChain :: Slot -> ChainIdeal -> Gen ChainIdeal
    genChain latest [] = fmap pure $ mkBlockIdeal <$> genParty <*> genSlot latest <*> pure Nothing <*> pure genesisHash
    genChain latest ancestors = do
      prefix <- flip drop ancestors <$> frequency [(9, pure 0), (1, getNonNegative <$> arbitrary)]
      -- FIXME: Generalize to add more than just one block to the prefix.
      extend <- nextBlock latest (finalSlot prefix) (hashTip prefix) ancestors
      pure $ extend prefix
    -- Generate an extension to a chain.
    nextBlock latest slot' hash' ancestors
      | latest >= slot' =
          fmap (:) $
            mkBlockIdeal
              <$> elements [slot' .. latest]
              <*> genParty
              <*> genHasCert slot' ancestors
              <*> pure hash'
      | otherwise = pure id
    -- Generate a certificate for a previous block.
    genCert latest ancestors = Certificate <$> genRound latest <*> (snd <$> genBlockRef ancestors)
    -- Geneate a vote for a previous block.
    genVote latest ancestors =
      do
        (s, h) <- genBlockRef ancestors
        -- FIXME: This may fail if `s > latest`.
        VoteIdeal <$> genParty <*> elements [s .. latest] <*> pure h
    -- Generate a reference to a block on a chain.
    genBlockRef :: ChainIdeal -> Gen (Slot, Hash Block)
    genBlockRef [] = pure (0, genesisHash)
    genBlockRef ancestors =
      frequency
        [ (9, pure . slotAndHash $ head ancestors)
        , (5, slotAndHash <$> elements ancestors)
        ]
     where
      slotAndHash b = (slot b, hash b)
    -- Generate a possible certificate up to the latest slot and of a block on a chain.
    genHasCert latest ancestors = frequency [(1, pure Nothing), (5, Just <$> genCert latest ancestors)]
    -- Generate a slot number up to the latest specified slot.
    genSlot latest = elements [0 .. latest]
    -- Generate a round up to the latest specified slot.
    genRound latest = elements [0 .. (latest `div` roundLength)]
    -- Generate a party ID.
    genParty = genNatural `suchThat` (/= self)
    -- Generate a natural number.
    genNatural = fromInteger . getNonNegative <$> arbitrary

  -- Sanity checks for the arbitrary actions.
  precondition NodeModel{self, now, protocol = Peras{roundLength}} =
    \case
      Initialize{} -> True
      ATick{} -> True
      ANewChain chain ->
        let checkChain _ [] = True
            checkChain time [block] = checkBlock time block
            checkChain time (block : blocks) =
              checkBlock time block
                && parent block == hash (head blocks)
                && checkChain (slot block - 1) blocks
         in checkChain now chain
      ASomeCert cert -> checkCert now cert
      ASomeVote vote -> checkVote now vote
   where
    checkBlock time BlockIdeal{creator, slot, cert} = creator /= self && slot <= time && maybe True (checkCert time) cert
    checkCert time Certificate{votingRoundNumber} = votingRoundNumber * roundLength <= time
    checkVote time VoteIdeal{voter, voteRound} = voter /= self && voteRound * roundLength <= time

  initialState = def

  nextState state@NodeModel{protocol} action _var =
    case action of
      Initialize protocol' self' -> state{self = self', protocol = protocol'}
      ATick isSlotLeader isCommitteeMember -> flip execState state $ nextSlot protocol isSlotLeader isCommitteeMember
      ANewChain chain -> flip execState state $ evaluateChain protocol chain
      ASomeCert cert -> flip execState state $ includeCert cert
      ASomeVote vote -> flip execState state $ includeVote protocol vote

deriving instance Eq (Action NodeModel a)
deriving instance Show (Action NodeModel a)

instance HasVariables (Action NodeModel a) where
  getAllVariables = mempty

--------------------------------------------------------------------------------

-- Real interface for Peras nodes

-- FIXME: This is a placeholder for the richer version of `PerasNode`.
-- TODO: Refine this instead of using the obsolete version in `peras-iosim`.
class Monad m => PerasNode a m where
  setOwner :: PartyId -> a -> m a
  setProtocol :: Protocol -> a -> m a
  newSlot :: IsSlotLeader -> IsCommitteeMember -> a -> m ([Message], a)
  newChain :: Chain -> a -> m ([Message], a)
  someCertificate :: Certificate -> a -> m ([Message], a)
  someVote :: Vote -> a -> m ([Message], a)

--------------------------------------------------------------------------------

-- Run monad

newtype RunMonad n m a = RunMonad {runMonad :: StateT n m a}
  deriving newtype (Functor, Applicative, Monad, MonadState n)

instance MonadTrans (RunMonad n) where
  lift = RunMonad . lift

-- instance Monad m => PerasNode n (RunMonad n m)

type instance Realized (RunMonad n m) () = ()
type instance Realized (RunMonad n m) [MessageIdeal] = [Message]

instance (Monad m, PerasNode n m) => RunModel NodeModel (RunMonad n m) where
  perform _state (Initialize protocol self) _context =
    put =<< lift . (setProtocol protocol <=< setOwner self) =<< get
  perform _state (ATick isSlotLeader isCommitteeMember) _context =
    apply $ newSlot isSlotLeader isCommitteeMember
  perform _state (ANewChain chain) _context =
    apply $ newChain (realizeChain chain)
  perform _state (ASomeCert cert) _context =
    apply $ someCertificate (realizeCert cert)
  perform _state (ASomeVote vote) _context =
    apply $ someVote (realizeVote vote)

  postcondition _ Initialize{} _ _ = pure True
  postcondition (prior, _) (ATick isSlotLeader isCommitteeMember) _env messages = do
    let idealMessages = flip evalState prior $ nextSlot (protocol prior) isSlotLeader isCommitteeMember
    pure $ identicalMessages messages idealMessages
  postcondition (prior, _) (ANewChain chain) _env messages = do
    let idealMessages = flip evalState prior $ evaluateChain (protocol prior) chain
    pure $ identicalMessages messages idealMessages
  postcondition (prior, _) (ASomeCert cert) _env messages = do
    let idealMessages = flip evalState prior $ includeCert cert
    pure $ identicalMessages messages idealMessages
  postcondition (prior, _) (ASomeVote vote) _env messages = do
    let idealMessages = flip evalState prior $ includeVote (protocol prior) vote
    pure $ identicalMessages messages idealMessages

identicalMessages :: [Message] -> [MessageIdeal] -> Bool
identicalMessages real ideal = on (==) sort ideal $ idealizeMessage `mapMaybe` real

apply :: (Monad m, MonadTrans t, MonadState s (t m)) => (s -> m (a, s)) -> t m a
apply f = do
  (x, s') <- lift . f =<< get
  put s'
  pure x

--------------------------------------------------------------------------------

-- Example implementation of a Peras node.

-- | Non-trivial set of Peras protocol parameters.
initialize :: Action NodeModel ()
initialize = Initialize Peras{roundLength = 10, quorum = 3, boost = 0.25} 0

data ExampleNode = ExampleNode
  { exOwner :: PartyId
  , exProtocol :: Protocol
  , exSlot :: Slot
  , exChain :: Chain
  , exCerts :: [Certificate]
  , exVotes :: [Vote]
  }
  deriving (Eq, Show)

instance Default ExampleNode where
  def = ExampleNode 0 def 0 mempty mempty mempty

-- TODO: Consider fixing the omissions so this buggy node becomes an honest one.
instance PerasNode ExampleNode Gen where
  setOwner party node = pure node{exOwner = party}
  setProtocol protocol node = pure node{exProtocol = protocol}
  newSlot isSlotLeader isCommitteeMember node =
    -- Known bug: Intentionally fails to forge and vote if both requested in the same slot.
    -- Known bug: Intentionally fails to issue a certificate if a quorum is reached.
    let previous = exChain node
        previousHash =
          if null previous
            then Hash mempty
            else Hash . Signature.bytes . Block.signature $ head previous
     in case (isSlotLeader, isCommitteeMember) of
          (True, _) -> do
            block <-
              Block
                (exSlot node)
                (exOwner node)
                previousHash
                Nothing -- Known bug: never includes a certificate.
                <$> arbitrary
                <*> arbitrary
                <*> arbitrary
            let chain = block : previous
            pure ([NewChain chain], node{exChain = chain})
          (_, True) -> do
            vote <-
              MkVote
                (MkRoundNumber $ exSlot node `div` roundLength (exProtocol node))
                (exOwner node)
                <$> arbitrary
                <*> pure previousHash
                <*> arbitrary
            pure ([SomeVote vote], node)
          _ -> pure ([], node)
  newChain chain node =
    -- Known bug: Intentionally fails to account for voting boost.
    pure $
      if length chain > length (exChain node)
        then ([NewChain chain], node{exChain = chain})
        else ([], node)
  someCertificate cert node =
    -- Known bug: Intentionally fails to only forward the certificate if it wasn't already seen.
    pure ([SomeCertificate cert], node{exCerts = exCerts node <> [cert]})
  someVote vote node =
    -- Known bug: Intentionally fails to only forward the vote if it wasn't already seen.
    -- Known bug: Intentionally fails to create a certificate if the vote creates a quorum.
    pure ([SomeVote vote], node{exVotes = exVotes node <> [vote]})
