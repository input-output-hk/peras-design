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
  NodeCosts (..),
  Node (Node),
) where

import Control.Lens (Lens', lens, use, uses, (%=), (&), (.=), (.~), (^.))
import Control.Monad (when, (<=<))
import Control.Monad.Class.MonadTime (addUTCTime)
import Control.Monad.Except (ExceptT (..), liftEither, runExceptT)
import Control.Monad.State (MonadState, StateT (runStateT), lift)
import Data.Aeson (FromJSON, ToJSON)
import Data.Default (Default (..))
import Data.Either (isRight)
import Data.List (partition)
import Data.Ratio ((%))
import Data.Set (Set)
import GHC.Generics (Generic)
import Generic.Random (genericArbitrary, uniform)
import Peras.Arbitraries ()
import Peras.Block (Block (..), BlockBody, PartyId)
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
  buildChain,
  eligibleDanglingVotes,
  lookupBlock,
  lookupBody,
  lookupVote,
  missingIncludedVotes,
  preferChain,
  resolveBlock,
 )
import Peras.IOSim.Chain.Types (ChainState (blockIndex, bodyIndex, preferredChain, voteIndex))
import Peras.IOSim.Crypto (
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

data NodeCosts = NodeCosts
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
  , costFollowChain :: CpuTime
  -- ^ Process a chain-following message.
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

instance FromJSON NodeCosts
instance ToJSON NodeCosts

instance Default NodeCosts where
  -- FIXME: Replace with realistic values.
  def =
    NodeCosts
      { costForgeBlock = fromRational $ 100_000 % 1_000_000
      , costCastVote = fromRational $ 100_001 % 1_000_000
      , costEvaluateChain = fromRational $ 100_002 % 1_000_000
      , costRollForward = fromRational $ 100_003 % 1_000_000
      , costRollBack = fromRational $ 100_004 % 1_000_000
      , costFollowChain = fromRational $ 100_005 % 1_000_000
      , costVerifyVote = fromRational $ 100_006 % 1_000_000
      , costVerifyBlock = fromRational $ 100_007 % 1_000_000
      , costVerifyBody = fromRational $ 100_008 % 1_000_000
      , costReportVote = fromRational $ 100_009 % 1_000_000
      , costReportBlock = fromRational $ 100_010 % 1_000_000
      , costReportBody = fromRational $ 100_011 % 1_000_000
      , costRecordVote = fromRational $ 100_012 % 1_000_000
      , costRecordBlock = fromRational $ 100_013 % 1_000_000
      , costRecordBody = fromRational $ 100_014 % 1_000_000
      , costRequestVote = fromRational $ 100_015 % 1_000_000
      , costRequestBlock = fromRational $ 100_016 % 1_000_000
      , costRequestBody = fromRational $ 100_017 % 1_000_000
      , costSendMessage = fromRational $ 100_018 % 1_000_000
      }

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

traceInvalid' ::
  NodeContext m ->
  String ->
  Invalid ->
  m ()
traceInvalid' NodeContext{traceSelf} location invalid =
  traceSelf $ A.object ["invalid" A..= invalid, "location" A..= location]

data Node = Node
  { nodeId :: NodeId
  , owner :: PartyId
  , stake :: Coin
  , vrfOutput :: Double
  , downstreams :: Set NodeId
  , chainState :: ChainState
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
        FollowChain hash -> followChain context' origin hash
        RollForward block -> roll context' (costRollForward def) origin block
        RollBack block -> roll context' (costRollBack def) origin block
        FetchVotes hashes -> fetchVotes context' origin hashes
        SomeVote vote -> newVote context' origin vote
        FetchBlocks hashes -> fetchBodies context' origin hashes
        SomeBlock body -> recordBody context' body
   where
    context' = hoistNodeContext lift context
  stop node NodeContext{traceSelf} =
    do
      traceSelf $ A.object ["finalState" A..= (node ^. chainStateLens)]
      pure node

-- | Whether to use `NewChain` messages for notifying downstream peers when a new chain is adopted: otherwise, `RollForward` and `RollBack` messages are sent.
legacyMode :: Bool
legacyMode = False

makeResultDownstreams ::
  MonadState Node m =>
  NodeContext m ->
  NodeStats ->
  [Message] ->
  m NodeResult
makeResultDownstreams context stats' messages =
  do
    peers <- uses downstreamsLens S.toList
    makeResult context stats' $ (,) <$> peers <*> messages

makeResult ::
  MonadState Node m =>
  NodeContext m ->
  NodeStats ->
  [(NodeId, Message)] ->
  m NodeResult
makeResult NodeContext{..} stats' messages =
  do
    source <- use nodeIdLens
    tip <- uses chainStateLens $ hashTip . blocks . preferredChain
    let
      messages' =
        flip filter messages $
          \case
            (_, FetchVotes []) -> False
            (_, FetchBlocks []) -> False
            _ -> True
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
          uncurry outEnvelope <$> messages'
      stats =
        stats'
          <> mempty
            { preferredTip = pure (slot, tip)
            , txBytes = sum $ messageSize . snd <$> messages'
            }
    pure NodeResult{..}

nextSlot ::
  MonadState Node m =>
  NodeContext m ->
  m NodeResult
nextSlot context@NodeContext{..} =
  do
    let
      Peras{..} = protocol
      r = currentRound protocol slot
      votingRound = isFirstSlotInRound protocol slot
    -- Discard expired votes.
    chainStateLens %= discardExpiredVotes protocol slot
    -- Update the VRF output.
    vrfOutputLens %= nextVrf
    vrf <- use vrfOutputLens
    -- Handle block production.
    leader <- isSlotLeader activeSlotCoefficient totalStake vrf <$> use stakeLens
    leaderResult <-
      if leader
        then doLeading context
        else pure mempty
    -- Handle voting.
    voter <- isCommitteeMember pCommitteeLottery totalStake vrf <$> use stakeLens
    votes <- uses chainStateLens $ voteInRound protocol r
    voterResult <-
      if votingRound && voter && votes
        then doVoting context r
        else pure mempty
    tip <- uses chainStateLens $ hashTip . blocks . preferredChain
    roundResult <- makeResultDownstreams context mempty{votingAllowed = if votingRound && votes then pure (r, tip) else mempty} mempty
    -- Report the results.
    pure $ leaderResult <> voterResult <> roundResult

doLeading ::
  MonadState Node m =>
  NodeContext m ->
  m NodeResult
doLeading context@NodeContext{slot} =
  do
    vrf <- use vrfOutputLens
    -- Forge the new block.
    block <-
      Block slot
        <$> use ownerLens
        <*> uses chainStateLens (hashTip . Peras.Chain.blocks . preferredChain)
        <*> uses chainStateLens eligibleDanglingVotes
        <*> pure (proveLeadership vrf ())
        <*> pure (signBlock vrf ())
        <*> pure (Hash $ randomBytes VrfBodyHash vrf)
    chainStateLens %= appendBlock block
    -- FIXME: Implement `prefixCutoffWeight` logic.
    preferred <- chainStateLens `uses` preferredChain
    makeResultDownstreams
      context
      mempty{slotLeader = pure slot, cpuTime = costForgeBlock def + costRecordBlock def}
      $ if legacyMode
        then [NewChain preferred] -- Send the whole chain downstream.
        else [RollForward block] -- Send only the new block header downstream.

doVoting ::
  MonadState Node m =>
  NodeContext m ->
  RoundNumber ->
  m NodeResult
doVoting context@NodeContext{protocol, slot} r =
  makeResultDownstreams context mempty{committeeMember = pure slot, cpuTime = costCastVote def + costRecordVote def} =<< do
    vrf <- use vrfOutputLens
    chainStateLens `uses` (blocksInWindow (candidateWindow protocol slot) . preferredChain)
      >>= \case
        block : _ -> do
          -- Cast the vote.
          vote <-
            MkVote r
              <$> use ownerLens
              <*> pure (proveMembership vrf ())
              <*> pure (hashBlock block)
              <*> pure (signVote vrf ())
          chainStateLens %= addVote vote
          -- Send the vote downstream.
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
    state' <- chainStateLens `uses` preferChain proposed'
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
        makeResultDownstreams
          context'
          mempty{cpuTime = costEvaluateChain def, rollbacks = checkRollback preferred proposed'}
          [NewChain preferred]
      else do
        messages <- newBlocksVotes proposed'
        chainStateLens %= addChain proposed'
        makeResultDownstreams context' mempty{cpuTime = costEvaluateChain def} messages

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

evaluateChain ::
  MonadState Node m =>
  NodeContext m ->
  NodeId ->
  Block ->
  m NodeResult
evaluateChain context@NodeContext{traceSelf} sender block =
  if legacyMode
    then pure mempty
    else
      chainStateLens `uses` buildChain block >>= \case
        -- Evaluate the chain if it could be constructed.
        Right chain -> do
          traceSelf $ A.object ["tag" A..= ("CHAIN FOUND" :: String), "block" A..= block, "chain" A..= chain]
          newChain context chain
        -- Request the missing blocks and votes if the chain could not be constructed.
        Left (blocksMissing, votesMissing) ->
          do
            traceSelf $ A.object ["tag" A..= ("CHAIN NOT FOUND" :: String), "block" A..= block, "blocksMissing" A..= blocksMissing, "votesMissing" A..= votesMissing]
            makeResult context mempty{cpuTime = costEvaluateChain def} $
              (sender,)
                <$> [FetchVotes votesMissing, FetchBlocks blocksMissing]

followChain ::
  MonadState Node m =>
  NodeContext m ->
  NodeId ->
  BlockHash ->
  m NodeResult
followChain context sender hash =
  do
    -- Finds the block subsequent to the intersection point.
    blocks <- uses chainStateLens $ reverse . takeWhile ((/= hash) . hashBlock) . blocks . preferredChain
    -- Send the blocks.
    makeResult context mempty{cpuTime = costFollowChain def} $
      (sender,) . RollForward <$> blocks

roll ::
  MonadState Node m =>
  NodeContext m ->
  CpuTime ->
  NodeId ->
  Block ->
  m NodeResult
roll context cpu sender block =
  do
    -- Process the block.
    blockResult <- newBlock context cpu sender block
    -- Determine whether to adopt a new chain.
    evaluateResult <- evaluateChain context sender block
    -- Report the result.
    pure $ blockResult <> evaluateResult

newBlock ::
  MonadState Node m =>
  NodeContext m ->
  CpuTime ->
  NodeId ->
  Block ->
  m NodeResult
newBlock context cpu sender block =
  chainStateLens `uses` lookupBlock (hashBlock block) >>= \case
    -- No action is required because this block has already been processed.
    Right _ -> pure mempty
    Left _ ->
      makeResult context mempty{cpuTime = cpu + costVerifyBlock def + costRecordBlock def} . fmap (sender,) =<< do
        -- Record the block.
        chainStateLens %= addBlock block
        -- Fetch any votes included in the block.
        message <- uses chainStateLens $ FetchVotes . missingIncludedVotes [block]
        either
          -- Fetch the block body if it hasn't already been fetched.
          (const [message, FetchBlocks [bodyHash block]])
          (const [message])
          <$> chainStateLens `uses` lookupBody (bodyHash block)

newVote ::
  MonadState Node m =>
  NodeContext m ->
  NodeId ->
  Vote ->
  m NodeResult
newVote context@NodeContext{protocol} sender vote =
  chainStateLens `uses` lookupVote (hashVote vote) >>= \case
    -- No action is required because this vote has already been processed.
    Right _ -> pure mempty
    Left _ -> do
      addValidVote protocol vote >>= \case
        -- Forward the vote downstream if the node is in legacy mode.
        Right _ ->
          if legacyMode || True
            then makeResultDownstreams context mempty{cpuTime = costVerifyVote def + costRecordVote def} [SomeVote vote]
            else makeResult context mempty{cpuTime = costVerifyVote def + costRecordVote def} mempty
        -- Fetch the block so that the vote can later be evaluated.
        Left e@HashOfUnknownBlock -> do
          traceInvalid' context "Peras.IOSim.Nodes.Honest.newVote" e
          makeResult context mempty{cpuTime = costVerifyVote def + costRecordVote def} [(sender, FetchBlocks [blockHash vote])]
        -- Report the receipt of an invalid vote.
        Left e -> do
          traceInvalid' context "Peras.IOSim.Nodes.Honest.newVote" e
          makeResult context mempty{cpuTime = costVerifyVote def + costRecordVote def} mempty

addValidVote ::
  MonadState Node m =>
  Protocol ->
  Vote ->
  m (Either Invalid ())
addValidVote protocol vote =
  do
    state <- use chainStateLens
    let result =
          do
            -- A vote can only be validated if it votes for a known block.
            block <- snd <$> resolveBlock state vote
            -- Ensure that the vote is not an equivocation.
            checkEquivocation state vote
            -- Validate the vote.
            validCandidateWindow protocol (vote, block)
    -- Record the vote.
    when (isRight result) $
      chainStateLens .= addVote vote state
    pure result

recordBody ::
  MonadState Node m =>
  NodeContext m ->
  BlockBody ->
  m NodeResult
recordBody context body =
  do
    -- Record the block body.
    chainStateLens %= addBody body
    -- Report the result.
    makeResultDownstreams context mempty{cpuTime = costVerifyBody def + costRecordBody def} mempty

fetchBodies ::
  MonadState Node m =>
  NodeContext m ->
  NodeId ->
  [BlockHash] ->
  m NodeResult
fetchBodies context requester hashes =
  do
    -- Find which block bodies are known.
    found <- uses chainStateLens $ flip M.restrictKeys (S.fromList hashes) . bodyIndex
    -- Send the block bodies.
    makeResult context mempty{cpuTime = fromIntegral (length hashes) * costReportBody def} $
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
    -- Find the votes which are known.
    found <- uses chainStateLens $ flip M.restrictKeys (S.fromList hashes) . voteIndex
    -- Send the votes.
    makeResult context mempty{cpuTime = fromIntegral (length hashes) * costReportVote def} $
      (requester,) . SomeVote
        <$> M.elems found
