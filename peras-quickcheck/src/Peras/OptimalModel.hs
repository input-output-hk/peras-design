{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

-- | A simple and early stage model for a Praos/Peras node and its environment.
module Peras.OptimalModel where

import Control.Monad.State (
  MonadState (get, put),
  MonadTrans (..),
  StateT (StateT),
 )
import Data.Default (Default (..))
import Data.Function (on)
import Data.List (sort)
import Numeric.Natural (Natural)
import Peras.Block (Block (Block, certificate, slotNumber), Certificate, Slot)
import Peras.Chain (Chain, Vote)
import Peras.Message (Message (..))
import Peras.Orphans ()
import Test.QuickCheck (frequency, sublistOf)
import Test.QuickCheck.DynamicLogic (DynLogicModel)
import Test.QuickCheck.StateModel (
  Any (Some),
  HasVariables (..),
  Realized,
  RunModel (perform, postcondition),
  StateModel (Action, arbitraryAction, initialState, nextState), -- (Any (..), HasVariables, PostconditionM, Realized, RunModel (..), StateModel (..), Var, counterexamplePost, monitorPost, Env(..))
 )

-- 1. state of the model to generate actions and traces
-- 2. need interesting actions
-- 3. define for each action
--     1. generator for action from state
--     2. transition function
--     3. precondition, often similar to generator (don't violate precondition)
--     4. (maybe) shrinkers
--     5. (later) negative preconditions
-- 4. run model
--     1. initial state
--     2. what each action does on the actual system under test ("perform")
--     3. postconditions (expected results)
-- 5. initially just "local" behavior of node with mock environment
-- 6. (later) global properties with multiple interacting nodes

type IsSlotLeader = Bool

data Protocol = Peras
  { roundLength :: Natural
  , quorum :: Int
  , boost :: Double
  }
  deriving (Eq, Ord, Show)

instance Default Protocol where
  def = Peras{roundLength = 1, quorum = maxBound, boost = 0}

type VoteIdeal = ()

newVote :: VoteIdeal
newVote = ()

realizeVote :: NodeModel -> VoteIdeal -> Vote
realizeVote = undefined -- FIXME: Implement!

idealizeVote :: Vote -> VoteIdeal
idealizeVote = const ()

type CertIdeal = ()

newCert :: CertIdeal
newCert = ()

realizeCert :: NodeModel -> CertIdeal -> Certificate
realizeCert = undefined -- FIXME: Implement!

idealizeCert :: Certificate -> CertIdeal
idealizeCert = const ()

data BlockIdeal = BlockIdeal
  { slot :: Slot
  , cert :: Maybe CertIdeal
  }
  deriving (Eq, Ord, Show)

realizeBlock :: NodeModel -> BlockIdeal -> Block
realizeBlock = undefined -- FIXME: Implement!

idealizeBlock :: Block -> BlockIdeal
idealizeBlock Block{slotNumber, certificate} = BlockIdeal{slot = slotNumber, cert = idealizeCert <$> certificate}

type ChainIdeal = [BlockIdeal]

realizeChain :: NodeModel -> ChainIdeal -> Chain
realizeChain = undefined -- FIXME: Implement!

idealizeChain :: Chain -> ChainIdeal
idealizeChain = fmap idealizeBlock

data NodeModel = NodeModel
  { protocol :: Protocol
  , now :: Slot
  , preferredChain :: ChainIdeal
  , preferredCerts :: [CertIdeal]
  , preferredVotes :: [VoteIdeal]
  }
  deriving (Eq, Ord, Show)

data MessageIdeal
  = NewChainIdeal ChainIdeal
  | SomeCertIdeal CertIdeal
  | SomeVoteIdeal VoteIdeal
  deriving (Eq, Ord, Show)

idealizeMessage :: Message -> MessageIdeal
idealizeMessage = undefined -- FIXME: Implement!

instance Default NodeModel where
  def = NodeModel def 0 def def def

instance HasVariables NodeModel where
  getAllVariables = mempty

instance DynLogicModel NodeModel

instance StateModel NodeModel where
  data Action NodeModel a where
    ATick :: IsSlotLeader -> Action NodeModel [MessageIdeal]
    ANewChain :: ChainIdeal -> Action NodeModel [MessageIdeal]
    ASomeCert :: CertIdeal -> Action NodeModel [MessageIdeal]
    ASomeVote :: VoteIdeal -> Action NodeModel [MessageIdeal]

  arbitraryAction _context NodeModel{now, preferredChain} =
    frequency
      [ (9, Some . ATick <$> genSlotLeader)
      , (6, Some . ANewChain . (: preferredChain) <$> genBlock now)
      , (1, fmap (Some . ANewChain) $ mapM genBlock =<< sublistOf [0 .. now])
      , (1, pure . Some $ ASomeCert newCert)
      , (2, pure . Some $ ASomeVote newVote)
      ]
   where
    genSlotLeader = frequency [(9, pure False), (1, pure True)]
    genHasCertificate = frequency [(1, pure Nothing), (5, pure $ Just newCert)]
    genBlock = (<$> genHasCertificate) . BlockIdeal

  -- FIXME: How can the initial state be set a runtime? Would we need a `SetState`
  -- action and then constrain that to be called first and only once?
  initialState = def{protocol = Peras{roundLength = 10, quorum = 3, boost = 0.25}}

  nextState state@NodeModel{protocol} action _var =
    case action of
      ATick False -> stepSlot state
      ATick True -> snd . issueBlock protocol $ stepSlot state
      -- FIXME: Adopting a new chain also involves adjusting the set of preferred
      -- certificates and votes.
      ANewChain chain ->
        if ((>) `on` chainLength (boost protocol)) chain (preferredChain state)
          then state{preferredChain = chain}
          else state
      ASomeCert cert -> includeCert cert state
      ASomeVote vote -> snd $ includeVote protocol vote state

stepSlot :: NodeModel -> NodeModel
stepSlot state = state{now = 1 + now state}

includeCert :: CertIdeal -> NodeModel -> NodeModel
includeCert cert state = state{preferredCerts = preferredCerts state <> pure cert}

includeVote :: Protocol -> VoteIdeal -> NodeModel -> ([MessageIdeal], NodeModel)
includeVote protocol vote state = issueCert protocol $ state{preferredVotes = preferredVotes state <> pure vote}

issueBlock :: Protocol -> NodeModel -> ([MessageIdeal], NodeModel)
issueBlock protocol state =
  let
    (voteMessages, state') = issueVote protocol state
    (cert, certs) =
      case preferredCerts state' of
        [] -> (Nothing, [])
        cert' : certs' -> (Just cert', certs')
    chain = BlockIdeal (now state') cert : preferredChain state'
   in
    ( voteMessages <> [NewChainIdeal chain]
    , state'{preferredChain = chain, preferredCerts = certs}
    )

issueCert :: Protocol -> NodeModel -> ([MessageIdeal], NodeModel)
issueCert Peras{quorum} state =
  if length (preferredVotes state) >= quorum
    then (pure $ SomeCertIdeal newCert, state{preferredCerts = preferredCerts state <> pure newCert, preferredVotes = mempty})
    else (mempty, state)

issueVote :: Protocol -> NodeModel -> ([MessageIdeal], NodeModel)
issueVote protocol@Peras{roundLength} state =
  -- FIXME: Sequence in an ephemeral `StateT`.
  let (voteMessages, state') =
        if now state `mod` roundLength == 0
          then (pure $ SomeVoteIdeal newVote, state{preferredVotes = preferredVotes state <> pure newVote})
          else (mempty, state)
      (certMessages, state'') = issueCert protocol state'
   in (certMessages <> voteMessages, state'')

deriving instance Eq (Action NodeModel a)
deriving instance Show (Action NodeModel a)

instance HasVariables (Action NodeModel a) where
  getAllVariables = mempty

chainLength :: Double -> ChainIdeal -> Double
chainLength boost' = sum . fmap (maybe 1 (const $ 1 + boost') . cert)

-- FIXME: This is a placeholder for the richer version of `PerasNode`.
class PerasNode a where
  newSlot :: Monad m => IsSlotLeader -> a -> m ([Message], a)
  newChain :: Monad m => Chain -> a -> m ([Message], a)
  someCertificate :: Monad m => Certificate -> a -> m ([Message], a)
  someVote :: Monad m => Vote -> a -> m ([Message], a)

newtype RunMonad n m a = RunMonad {runMonad :: StateT n m a}
  deriving newtype (Functor, Applicative, Monad, MonadState n)

instance MonadTrans (RunMonad n) where
  lift = RunMonad . lift

type instance Realized (RunMonad n m) [MessageIdeal] = [Message]

apply :: MonadState s m => (s -> m (a, s)) -> m a
apply f = do
  (x, s') <- f =<< get
  put s'
  pure x

instance (Monad m, PerasNode n) => RunModel NodeModel (RunMonad n m) where
  perform _state (ATick isSlotLeader) _context =
    apply $ newSlot isSlotLeader
  perform state (ANewChain chain) _context =
    apply $ newChain (realizeChain state chain)
  perform state (ASomeCert cert) _context =
    apply $ someCertificate (realizeCert state cert)
  perform state (ASomeVote vote) _context =
    apply $ someVote (realizeVote state vote)

  postcondition (prior, posterior) (ATick False) _env messages =
    -- FIXME: How can we use `posterior === prior` here?
    pure $ posterior == prior && null messages
  postcondition (prior, posterior) (ATick True) _env messages = do
    let (idealMessages, idealState) = issueBlock (protocol prior) prior
    pure $ posterior == idealState && sameMessages messages idealMessages
  postcondition (prior, posterior) (ANewChain) _env messages = do
    undefined -- FIXME: Implement.
  postcondition (prior, posterior) (ASomeCert cert) _env messages = do
    let idealState = includeCert cert prior
        -- FIXME: Implement certificate-forwarding logic.
        idealMessages = mempty
    pure $ posterior == idealState && sameMessages messages idealMessages
  postcondition (prior, posterior) (ASomeVote vote) _env messages = do
    let (idealMessages, idealState) = includeVote (protocol prior) vote prior
    pure $ posterior == idealState && sameMessages messages idealMessages

sameMessages :: [Message] -> [MessageIdeal] -> Bool
sameMessages real ideal = on (==) sort ideal $ idealizeMessage <$> real

{-
optimal : ∀ (c : Chain) (t : tT) (sl : Slot)
  → let b = bestChain sl t
    in
    ValidChain {block₀} {IsSlotLeader} {IsBlockSignature} c
  → c ⊆ allBlocksUpTo sl t
  → ∥ c , certs t c ∥ ≤ ∥ b , certs t b ∥
-}
