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
import Control.Monad (when)
import Control.Monad.Class.MonadTime (addUTCTime)
import Control.Monad.Except (ExceptT (..), liftEither, runExceptT)
import Control.Monad.State (MonadState, StateT (runStateT), lift)
import Data.Aeson (FromJSON, ToJSON)
import Data.Default (Default (..))
import Data.Either (isRight)
import Data.Foldable (toList)
import Data.Function (on)
import Data.List (group, maximumBy, partition, sort)
import Data.Ratio ((%))
import Data.Set (Set)
import GHC.Generics (Generic)
import Generic.Random (genericArbitrary, uniform)
import Peras.Arbitraries ()
import Peras.Block (Block (..), BlockBody (BlockBody), Certificate (Certificate), PartyId)
import Peras.Chain (Chain, RoundNumber (roundNumber), Vote (..))
import Peras.Crypto (Hash (Hash))
import Peras.Event (ByteSize, CpuTime, Rollback (..))
import Peras.IOSim.Chain
import Peras.IOSim.Crypto (
  VrfUsage (VrfBodyHash),
  nextVrf,
  proveLeadership,
  proveMembership,
  randomBytes,
  signBlock,
  signVote,
 )
import Peras.IOSim.Hash (BlockHash, ChainHash, VoteHash, castHash, hashBlock, hashTip, hashVote)
import Peras.IOSim.Message.Types (InEnvelope (..), OutEnvelope (..), messageSize, mkUniqueId)
import Peras.IOSim.Node.Types (NodeContext (..), NodeResult (..), NodeStats (..), PerasNode (..), TraceSelf, hoistNodeContext)
import Peras.IOSim.Protocol.Types (Protocol (..))
import Peras.IOSim.Types (Coin)
import Peras.Message (Message (..), NodeId)
import Test.QuickCheck (Arbitrary (..))

import qualified Data.Aeson as A
import qualified Data.Map as M
import qualified Data.Set as S

{-
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
-}

data Node = Node
  { nodeId :: NodeId
  , owner :: PartyId
  , stake :: Coin
  , nicBandwidth :: ByteSize
  , vrfOutput :: Double
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

nicBandwidthLens :: Lens' Node ByteSize
nicBandwidthLens = lens nicBandwidth $ \s x -> s{nicBandwidth = x}

vrfOutputLens :: Lens' Node Double
vrfOutputLens = lens vrfOutput $ \s x -> s{vrfOutput = x}

chainStateLens :: Lens' Node ChainState
chainStateLens = lens chainState $ \s x -> s{chainState = x}

instance PerasNode Node where
  getNodeId = nodeId
  getOwner = owner
  getStake = stake
  setStake node = (node &) . (stakeLens .~)
  getDownstreams = downstreams
  getPreferredChain = preferredChain . tracker . chainState
  getPreferredVotes = toList . preferredVotes . tracker . chainState
   where
    {-
      handleMessage node NodeContext{clock} Stop = pure (mempty{wakeup = clock}, node)
      handleMessage node context InEnvelope{..} =
        flip runStateT node $
          adjustMessageDelays context' inMessage
            =<< case inMessage of
              NextSlot _ -> nextSlot context'
              NewChain chain -> newChain context' chain
              FollowChain hash -> followChain context' origin hash
              RollForward block -> roll context' (costRollForward def) origin block
              RollBack block -> roll context' (costRollBack def) origin block
              FetchVotes hashes -> fetchVotes context' origin hashes
              SomeVote vote ->
                if False -- FIXME: Supress propagation of votes because the deficiency in the Agda certificate type makes that meaningless.
                  then newVote context' origin vote
                  else pure mempty
              FetchBlocks hashes -> fetchBodies context' origin hashes
              SomeBlock body -> recordBody context' body
              SomeCertificate{} -> error "Certificate messages are not yet supported." -- FIXME
    -}

    context' = hoistNodeContext lift context
  stop node NodeContext{traceSelf} =
    do
      traceSelf $ A.object ["finalState" A..= (node ^. chainStateLens)]
      pure node

{-
adjustMessageDelays ::
  MonadState Node m =>
  NodeContext m ->
  Message ->
  NodeResult ->
  m NodeResult
adjustMessageDelays NodeContext{slot} message result@NodeResult{..} =
  do
    tip <- uses chainStateLens $ hashTip . preferredChain
    bandwidth <- use nicBandwidthLens
    let individualDelays = fromRational . (/ fromIntegral bandwidth) . (% 1_000_000) . fromIntegral . messageSize . outMessage <$> outputs
        cumulativeDelays = scanl1 (+) individualDelays
        delayMessage output delay = output{outTime = delay `addUTCTime` outTime output}
        outputs' = zipWith delayMessage outputs cumulativeDelays
    pure
      result
        { wakeup -- FIXME: Whether to adjust `wakeup` depends upon threading assumptions.
        , outputs = outputs'
        , stats = stats{preferredTip = pure (slot, tip), rxBytes = messageSize message}
        }

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
    let messages' =
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
        outputs = uncurry outEnvelope <$> messages'
        stats = stats' <> mempty{txBytes = sum $ messageSize . snd <$> messages'}
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
    tip <- uses chainStateLens $ hashTip . preferredChain
    roundResult <- makeResultDownstreams context mempty{votingAllowed = if votingRound && votes then pure (r, tip) else mempty} mempty
    -- Report the results.
    pure $ leaderResult <> voterResult <> roundResult

doLeading ::
  MonadState Node m =>
  NodeContext m ->
  m NodeResult
doLeading context@NodeContext{slot} =
  do
    let makeCertificate :: [Vote] -> Maybe Certificate
        makeCertificate [] = Nothing
        makeCertificate votes =
          Just
            . uncurry Certificate
            . head
            . maximumBy (on compare length)
            . group
            . sort
            $ (\MkVote{..} -> (roundNumber votingRound, blockHash)) <$> votes
    vrf <- use vrfOutputLens
    -- Forge the new block.
    block <-
      Block slot
        <$> use ownerLens
        <*> uses chainStateLens (hashTip . preferredChain)
        <*> uses chainStateLens (makeCertificate . eligibleDanglingVotes)
        <*> pure (proveLeadership vrf ())
        <*> pure (signBlock vrf ())
        <*> pure (Hash $ randomBytes VrfBodyHash vrf)
    chainStateLens %= appendBlock block
    chainStateLens %= addBody (BlockBody (bodyHash block) mempty)
    -- FIXME: Implement `prefixCutoffWeight` logic.
    makeResultDownstreams
      context
      mempty{slotLeader = pure slot, cpuTime = costForgeBlock def + costRecordBlock def}
      [RollForward block]

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
    state' <- chainStateLens `uses` preferChain proposed
    -- FIXME: Currently it is impossible to know which votes are referenced by a certificate.
    liftEither $ validChain protocol state'
    let toWeight = chainWeight protocol state'
        checkRollback olds news =
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
        oldBlocks <- uses chainStateLens preferredChain
        let forwardBlocks = filter (`notElem` oldBlocks) proposed
        chainStateLens .= state'
        preferred <- chainStateLens `uses` preferredChain
        let rollbacks' = checkRollback preferred proposed
        if null rollbacks'
          then do
            makeResultDownstreams context' mempty{cpuTime = costEvaluateChain def}
              . reverse
              $ RollForward <$> forwardBlocks
          else
            makeResultDownstreams
              context'
              mempty{cpuTime = costEvaluateChain def, rollbacks = rollbacks'}
              [RollBack $ head proposed]
      else
        makeResultDownstreams context' mempty{cpuTime = costEvaluateChain def}
          =<< do
            chainStateLens %= addChain proposed
            pure mempty

evaluateChain ::
  MonadState Node m =>
  NodeContext m ->
  NodeId ->
  Block ->
  m NodeResult
evaluateChain context sender block =
  chainStateLens `uses` buildChain block >>= \case
    -- Evaluate the chain if it could be constructed.
    Right chain -> newChain context chain
    -- Request the missing blocks and votes if the chain could not be constructed.
    Left blocksMissing ->
      -- FIXME: Currently it is impossible to know what votes are missing.
      let votesMissing = mempty
       in makeResult context mempty{cpuTime = costEvaluateChain def} $
            (sender,)
              <$> [FetchVotes votesMissing, FetchBlocks blocksMissing]

followChain ::
  MonadState Node m =>
  NodeContext m ->
  NodeId ->
  ChainHash ->
  m NodeResult
followChain context sender hash =
  do
    -- Finds the block subsequent to the intersection point.
    blocks <- uses chainStateLens $ reverse . takeWhile ((/= castHash hash) . hashBlock) . preferredChain
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
        -- FIXME: Currently it is impossible to know which votes a certificate references.
        either
          -- Fetch the block body if it hasn't already been fetched.
          (const [FetchBlocks [hashBlock block]])
          (const [])
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
          makeResultDownstreams context mempty{cpuTime = costVerifyVote def + costRecordVote def} [SomeVote vote]
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
    hashes' <- uses chainStateLens $ fmap bodyHash . M.elems . flip M.restrictKeys (S.fromList hashes) . blockIndex
    found <- uses chainStateLens $ flip M.restrictKeys (S.fromList hashes') . bodyIndex
    -- Send the block bodies.
    makeResult context mempty{cpuTime = fromIntegral (length hashes) * costReportBody def} $
      (requester,) . SomeBlock <$> M.elems found

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
-}
