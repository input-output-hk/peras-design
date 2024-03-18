{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

module Peras.IOSim.Nodes.Honest (
  CostModel (..),
  Node (Node),
) where

import Control.Lens (Lens', lens, use, uses, (%=), (&), (.=), (.~), (^.))
import Control.Monad ((<=<))
import Control.Monad.Class.MonadTime (addUTCTime)
import Control.Monad.Except (ExceptT (ExceptT), MonadError (throwError), liftEither, runExceptT)
import Control.Monad.State (MonadState, lift, runStateT)
import Data.Aeson (FromJSON, ToJSON)
import Data.Default (Default (..))
import Data.List (partition)
import Data.Ratio ((%))
import Data.Set (Set)
import GHC.Generics (Generic)
import Generic.Random (genericArbitrary, uniform)
import Peras.Arbitraries ()
import Peras.Block (Block (..), BlockBody, PartyId, Slot)
import Peras.Chain (Chain (..), RoundNumber, Vote (..))
import Peras.Crypto (Hash (Hash))
import Peras.Event (CpuTime, Rollback (..))
import Peras.IOSim.Chain (
  Invalid (EquivocatedVote, HashOfUnknownBlock),
  addBlock,
  addBody,
  addChain,
  addVote,
  appendBlock,
  blocksInWindow,
  eligibleDanglingVotes,
  lookupBlock,
  lookupVote,
  preferChain,
  resolveBlock,
 )
import Peras.IOSim.Chain.Types (ChainState (blockIndex, bodyIndex, preferredChain, voteIndex))
import Peras.IOSim.Crypto (
  VrfOutput,
  VrfUsage (VrfBodyHash),
  nextVrf,
  proveLeadership,
  proveMembership,
  randomBytes,
  signBlock,
  signVote,
 )
import Peras.IOSim.Hash (BlockHash, VoteHash, hashBlock, hashTip, hashVote)
import Peras.IOSim.Message.Types (InEnvelope (..), OutEnvelope (..), messageSize, mkUniqueId)
import Peras.IOSim.Node.Types (NodeContext (..), NodeResult (..), NodeStats (..), PerasNode (..), TraceSelf, hoistNodeContext)
import Peras.IOSim.Protocol (
  candidateWindow,
  chainWeight,
  checkEquivocation,
  currentRound,
  discardExpiredVotes,
  isCommitteeMember,
  isFirstSlotInRound,
  isSlotLeader,
  validCandidateWindow,
  validChain,
  voteInRound,
 )
import Peras.IOSim.Protocol.Types (Protocol (..))
import Peras.IOSim.Types (Coin)
import Peras.Message (Message (..), NodeId)
import Test.QuickCheck (Arbitrary (..))

import qualified Data.Aeson as A
import qualified Data.Map as M
import qualified Data.Set as S

data CostModel = CostModel
  { costForgeBlock :: CpuTime
  -- ^ Slot leader forges a new block.
  , costCastVote :: CpuTime
  -- ^ Committee member casts a vote.
  , costEvaluateChain :: CpuTime
  -- ^ Weight a chain for adoption.
  , costRollForward :: CpuTime
  -- ^ Process
  , costRollBack :: CpuTime
  -- ^ Process a rollback message.
  , costVerifyVote :: CpuTime
  -- ^ Verify the validity of a vote.
  , costVerifyBlock :: CpuTime
  -- ^ Verify the validity of a block header.
  , costVerifyBody :: CpuTime
  -- ^ Verify the validity of a block body.
  , costReportVote :: CpuTime
  -- ^ Retrieve a vote from a local index.
  , costReportBlock :: CpuTime
  -- ^ Retrieve a block header from a local index.
  , costReportBody :: CpuTime
  -- ^ Retrieve a block body for a local index.
  , costRecordVote :: CpuTime
  -- ^ Store a vote in a local index.
  , costRecordBlock :: CpuTime
  -- ^ Store a block header in a local.
  , costRecordBody :: CpuTime
  -- ^ Store a block body in  a local
  , costRequestVote :: CpuTime
  -- ^ Decide to request a vote.
  , costRequestBlock :: CpuTime
  -- ^ Decide to request a block header.
  , costRequestBody :: CpuTime
  -- ^ Decide to request a block body.
  , costSendMessage :: CpuTime
  -- ^ Buffer and send a message to another node.
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON CostModel
instance ToJSON CostModel

instance Default CostModel where
  -- FIXME: Replace with realistic values.
  def =
    CostModel
      { costForgeBlock = fromRational $ 100_000 % 1_000_000
      , costCastVote = fromRational $ 100_001 % 1_000_000
      , costEvaluateChain = fromRational $ 100_002 % 1_000_000
      , costRollForward = fromRational $ 100_003 % 1_000_000
      , costRollBack = fromRational $ 100_004 % 1_000_000
      , costVerifyVote = fromRational $ 100_005 % 1_000_000
      , costVerifyBlock = fromRational $ 100_006 % 1_000_000
      , costVerifyBody = fromRational $ 100_007 % 1_000_000
      , costReportVote = fromRational $ 100_008 % 1_000_000
      , costReportBlock = fromRational $ 100_009 % 1_000_000
      , costReportBody = fromRational $ 100_010 % 1_000_000
      , costRecordVote = fromRational $ 100_011 % 1_000_000
      , costRecordBlock = fromRational $ 100_012 % 1_000_000
      , costRecordBody = fromRational $ 100_013 % 1_000_000
      , costRequestVote = fromRational $ 100_014 % 1_000_000
      , costRequestBlock = fromRational $ 100_015 % 1_000_000
      , costRequestBody = fromRational $ 100_016 % 1_000_000
      , costSendMessage = fromRational $ 100_017 % 1_000_000
      }

uses' :: MonadError e m => MonadState s m => Lens' s a -> (a -> Either e b) -> m b
uses' l f = uses l f >>= liftEither

(%#=) :: MonadError e m => MonadState s m => Lens' s a -> (a -> Either e a) -> m ()
l %#= f = uses l f >>= either throwError (l .=)

traceInvalid ::
  Monad m =>
  String ->
  a ->
  ExceptT Invalid m a ->
  TraceSelf m ->
  m a
traceInvalid location def' x trace =
  runExceptT x
    >>= \case
      Right result -> pure result
      Left invalid -> do
        trace $
          A.object
            [ "invalid" A..= invalid
            , "location" A..= location
            ]
        pure def'

data Node = Node
  { nodeId :: NodeId
  , owner :: PartyId
  , stake :: Coin
  , vrfOutput :: Double
  , chainState :: ChainState
  , downstreams :: Set NodeId
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON Node
instance ToJSON Node

instance Arbitrary Node where
  arbitrary = genericArbitrary uniform

nodeIdLens :: Lens' Node NodeId
nodeIdLens = lens nodeId $ \s x -> s{nodeId = x}

ownerLens :: Lens' Node PartyId
ownerLens = lens owner $ \s x -> s{owner = x}

stakeLens :: Lens' Node Coin
stakeLens = lens stake $ \s x -> s{stake = x}

vrfOutputLens :: Lens' Node Double
vrfOutputLens = lens vrfOutput $ \s x -> s{vrfOutput = x}

chainStateLens :: Lens' Node ChainState
chainStateLens = lens chainState $ \s x -> s{chainState = x}

downstreamsLens :: Lens' Node (Set NodeId)
downstreamsLens = lens downstreams $ \s x -> s{downstreams = x}

instance PerasNode Node where
  getNodeId = nodeId
  getOwner = owner
  getStake = stake
  setStake node = (node &) . (stakeLens .~)
  getDownstreams = downstreams
  getPreferredChain = preferredChain . chainState
  getBlocks = blockIndex . chainState
  getVotes = voteIndex . chainState
  handleMessage node context InEnvelope{..} =
    flip runStateT node $
      case inMessage of
        NextSlot _ -> nextSlot context'
        NewChain chain -> newChain context' chain
        SomeVote vote -> newVote context' vote
        FetchVotes hashes -> fetchVotes context' origin hashes
        FollowChain hash -> followChain context' origin hash
        RollForward block -> newBlock context' block
        RollBack block -> rollBackward context' origin block
        FetchBlocks hashes -> fetchBodies context' origin hashes
        SomeBlock body -> recordBody context' body
   where
    context' = hoistNodeContext lift context
  stop node NodeContext{traceSelf} =
    do
      traceSelf $ A.object ["finalState" A..= (node ^. chainStateLens)]
      pure node

-- FIXME / TODO:
-- 1. Consider using `These` instead of `Either` for graceful reporting of incomplete indices.
-- 2. Review each function in this file:
--    - Add cpu resource consumption.
--    - Request missing blocks, bodies, and votes.
--    - Cache messages that cannot be processed until blocks, votes, or bodies are received.
--    - `FollowChain` should trigger a stream of `RollForward`s.
--    - `RollForward` should act as an incremental version of `NewChain`.
--    - A rollback should trigger a `Rollback` message.
-- 3. Add toggle for `NewChain` mode vs `RollForward`/`Rollback`/`FollowChain` mode.
--
makeResult ::
  MonadState Node m =>
  NodeContext m ->
  NodeStats ->
  [Message] ->
  m NodeResult
makeResult context stats' messages =
  do
    peers <- uses downstreamsLens S.toList
    makeResult' context stats' $ (,) <$> peers <*> messages

makeResult' ::
  MonadState Node m =>
  NodeContext m ->
  NodeStats ->
  [(NodeId, Message)] ->
  m NodeResult
makeResult' NodeContext{..} stats' messages =
  do
    source <- use nodeIdLens
    tip <- uses chainStateLens $ hashTip . blocks . preferredChain
    let
      wakeup = cpuTime stats `addUTCTime` clock
      outTime = wakeup
      outEnvelope destination outMessage =
        OutEnvelope{..}
       where
        outId = mkUniqueId (outTime, source, destination, outMessage)
        outBytes = messageSize outMessage
      -- Send the messages in order, and not simultaneously.
      outputs =
        -- FIXME: Add realistic delays.
        zipWith (\i out -> out{outTime = fromRational (10 * i % 1_000_000) `addUTCTime` outTime}) [1 ..] $
          uncurry outEnvelope <$> messages
      stats =
        stats'
          <> mempty
            { preferredTip = pure (slot, tip)
            , --          , txBytes = sum $ outBytes <$> outputs  -- FIXME: Why does this fail with `<<loop>>`?
              txBytes = sum $ messageSize . snd <$> messages
            }
    pure NodeResult{..}

nextSlot :: MonadState Node m => NodeContext m -> m NodeResult
nextSlot context@NodeContext{..} =
  do
    let
      Peras{..} = protocol
      r = currentRound protocol slot
      votingRound = isFirstSlotInRound protocol slot
    chainStateLens %= discardExpiredVotes protocol slot
    vrfOutputLens %= nextVrf
    vrf <- use vrfOutputLens
    leader <- isSlotLeader activeSlotCoefficient totalStake vrf <$> use stakeLens
    leaderMessages <-
      if leader
        then doLeading slot vrf traceSelf
        else pure mempty
    voter <- isCommitteeMember pCommitteeLottery totalStake vrf <$> use stakeLens
    votes <- uses chainStateLens $ voteInRound protocol r
    voterMessages <-
      if votingRound && voter && votes
        then doVoting protocol slot r vrf traceSelf
        else pure mempty
    tip <- uses chainStateLens $ hashTip . blocks . preferredChain
    makeResult
      context
      mempty
        { slotLeader = if leader then pure slot else mempty
        , committeeMember = if votingRound && voter then pure slot else mempty
        , votingAllowed = if votingRound && votes then pure (r, tip) else mempty
        , cpuTime = fromRational $ 201_000 % 1_000_000 -- FIXME: Use realistic CPU times.
        }
      $ leaderMessages <> voterMessages

doLeading ::
  MonadState Node m =>
  Slot ->
  VrfOutput ->
  TraceSelf m ->
  m [Message]
doLeading slotNumber vrf =
  traceInvalid "Peras.IOSim.Nodes.Honest.doLeading" mempty $ do
    -- FIXME: Move toe `Peras.IOSim.Protocol`.
    block <-
      Block slotNumber
        <$> use ownerLens
        <*> uses chainStateLens (hashTip . Peras.Chain.blocks . preferredChain)
        <*> uses' chainStateLens eligibleDanglingVotes
        <*> pure (proveLeadership vrf ())
        <*> pure (signBlock vrf ())
        <*> pure (Hash $ randomBytes VrfBodyHash vrf)
    chainStateLens %#= appendBlock block
    -- FIXME: Implement `prefixCutoffWeight` logic.
    uses chainStateLens $ pure . NewChain . preferredChain

doVoting ::
  MonadState Node m =>
  Protocol ->
  Slot ->
  RoundNumber ->
  VrfOutput ->
  TraceSelf m ->
  m [Message]
doVoting protocol slotNumber r vrf =
  traceInvalid "Peras.IOSim.Nodes.Honest.doVoting" mempty $ do
    chainStateLens `uses` (blocksInWindow (candidateWindow protocol slotNumber) . preferredChain)
      >>= \case
        block : _ -> do
          vote <-
            -- FIXME: Move to `Peras.IOSim.Protocol`.
            MkVote r
              <$> use ownerLens
              <*> pure (proveMembership vrf ())
              <*> pure (hashBlock block)
              <*> pure (signVote vrf ())
          addValidVote protocol vote
          pure [SomeVote vote]
        [] -> pure mempty

newChain ::
  MonadState Node m =>
  NodeContext m ->
  Chain ->
  m NodeResult
newChain context@NodeContext{..} proposed =
  -- FIXME: Should the whole chain be rejected if any part of it or the its dangling votes is invalid?
  flip (traceInvalid "Peras.IOSim.Nodes.Honest.newChain" mempty) traceSelf $ do
    let context' = hoistNodeContext (ExceptT . fmap Right) context
    fromWeight <- chainStateLens `uses` chainWeight protocol
    notEquivocated <- uses chainStateLens $ ((/= Left EquivocatedVote) .) . checkEquivocation
    let proposed' = proposed{votes = filter notEquivocated $ votes proposed}
    state' <- chainStateLens `uses'` preferChain proposed'
    liftEither $ do
      validChain protocol state'
      mapM_ (validCandidateWindow protocol <=< resolveBlock state') $ votes proposed'
    let toWeight = chainWeight protocol state'
        checkRollback MkChain{blocks = olds} MkChain{blocks = news} =
          partition (`elem` news) olds
            & \case
              (_, []) -> mempty
              (prefix, suffix) ->
                let
                  atSlot = if null prefix then 0 else slotNumber $ head prefix
                  slotsRolledBack = slotNumber (head suffix) - atSlot
                  blocksRolledBack = fromIntegral $ length suffix
                 in
                  pure Rollback{..}
    if toWeight > fromWeight
      then do
        chainStateLens .= state'
        preferred <- chainStateLens `uses` preferredChain
        makeResult
          context'
          mempty
            { cpuTime = fromRational $ 202_000 % 1_000_000 -- FIXME: Use realistic CPU times.
            , rollbacks = checkRollback preferred proposed'
            }
          [NewChain preferred]
      else do
        messages <- newBlocksVotes proposed'
        chainStateLens %#= addChain proposed'
        makeResult
          context'
          mempty
            { cpuTime = fromRational $ 203_000 % 1_000_000 -- FIXME: Use realistic CPU times.
            }
          messages

newBlock ::
  MonadState Node m =>
  NodeContext m ->
  Block ->
  m NodeResult
newBlock context@NodeContext{..} block =
  traceInvalid "Peras.IOSim.Nodes.Honest.newBlock" mempty (newBlock' protocol block) traceSelf
    >>= makeResult
      context
      mempty
        { cpuTime = fromRational $ 204_000 % 1_000_000 -- FIXME: Use realistic CPU times.
        }

newBlock' ::
  MonadError Invalid m =>
  MonadState Node m =>
  Protocol ->
  Block ->
  m [Message]
newBlock' _ block =
  do
    chainStateLens `uses` lookupBlock (hashBlock block)
      >>= \case
        Right _ -> pure mempty
        Left _ -> do
          chainStateLens %#= addBlock block
          pure [RollForward block]

newVote ::
  MonadState Node m =>
  NodeContext m ->
  Vote ->
  m NodeResult
newVote context@NodeContext{..} vote =
  traceInvalid "Peras.IOSim.Nodes.Honest.newVote" mempty (newVote' protocol vote) traceSelf
    >>= makeResult
      context
      mempty
        { cpuTime = fromRational $ 205_000 % 1_000_000 -- FIXME: Use realistic CPU times.
        }

newVote' ::
  MonadError Invalid m =>
  MonadState Node m =>
  Protocol ->
  Vote ->
  m [Message]
newVote' protocol vote =
  do
    chainStateLens `uses` lookupVote (hashVote vote)
      >>= \case
        Right _ -> pure mempty
        Left _ -> do
          addValidVote protocol vote
          chainStateLens `uses` lookupBlock (blockHash vote)
            >>= \case
              Right block -> pure [SomeVote vote, RollForward block, SomeVote vote]
              Left HashOfUnknownBlock -> pure [SomeVote vote] -- FIXME: Ideally, we should request the block from the peers.
              Left e -> throwError e

newBlocksVotes ::
  MonadState Node m =>
  Chain ->
  m [Message]
newBlocksVotes (MkChain blocks votes) =
  do
    chain <- use chainStateLens
    let newBlocks = RollForward <$> filter (flip M.notMember (blockIndex chain) . hashBlock) blocks
        newVotes = SomeVote <$> filter (flip M.notMember (voteIndex chain) . hashVote) votes
    pure $ newBlocks <> newVotes

addValidVote ::
  MonadError Invalid m =>
  MonadState Node m =>
  Protocol ->
  Vote ->
  m ()
addValidVote protocol vote =
  do
    state <- use chainStateLens
    block <- liftEither $ snd <$> resolveBlock state vote
    liftEither $ do
      checkEquivocation state vote
      validCandidateWindow protocol (vote, block)
    state' <- liftEither $ addVote (vote, block) state
    chainStateLens .= state'

followChain ::
  MonadState Node m =>
  NodeContext m ->
  NodeId ->
  BlockHash ->
  m NodeResult
followChain context _sender _hash =
  do
    -- FIXME: Implement.
    makeResult context mempty mempty

rollBackward ::
  MonadState Node m =>
  NodeContext m ->
  NodeId ->
  Block ->
  m NodeResult
rollBackward context@NodeContext{traceSelf} _sender block =
  do
    flip (traceInvalid "Peras.IOSim.Nodes.Honest.rollBackward" mempty) traceSelf $
      chainStateLens %#= addBlock block
    makeResult context mempty mempty

recordBody ::
  MonadState Node m =>
  NodeContext m ->
  BlockBody ->
  m NodeResult
recordBody context@NodeContext{traceSelf} body =
  do
    flip (traceInvalid "Peras.IOSim.Nodes.Honest.recordBody" mempty) traceSelf $
      chainStateLens %#= addBody body
    makeResult context mempty mempty

fetchBodies ::
  MonadState Node m =>
  NodeContext m ->
  NodeId ->
  [BlockHash] ->
  m NodeResult
fetchBodies context requester hashes =
  do
    found <- uses chainStateLens $ flip M.restrictKeys (S.fromList hashes) . bodyIndex
    makeResult' context mempty $
      (requester,) . SomeBlock
        <$> M.elems found

fetchVotes ::
  MonadState Node m =>
  NodeContext m ->
  NodeId ->
  [VoteHash] ->
  m NodeResult
fetchVotes context requester hashes =
  do
    found <- uses chainStateLens $ flip M.restrictKeys (S.fromList hashes) . voteIndex
    makeResult' context mempty $
      (requester,) . SomeVote
        <$> M.elems found
