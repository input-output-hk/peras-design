{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Protocol (
  candidateWindow,
  chainWeight,
  currentRound,
  firstSlotInRound,
  inclusionWindow,
  isFirstSlotInRound,
  newBlock,
  newChain,
  newVote,
  nextSlot,
  quorumOnChain,
  roundNumber,
  validCandidate,
  validChain,
  validInclusion,
  validPraos,
  validVote,
  voteInRound,
) where

import Control.Lens (Lens', use, uses, (%=), (&), (.=))
import Control.Monad (forM_, unless, (<=<))
import Control.Monad.Class.MonadSay (MonadSay (..))
import Control.Monad.Except (
  ExceptT,
  MonadError (throwError),
  liftEither,
  runExceptT,
 )
import Control.Monad.IOSim.Orphans ()
import Control.Monad.State (MonadState)
import Data.Function (on)
import Data.List (partition)
import Debug.Trace
import Peras.Block (Block (Block, slotNumber), Slot)
import Peras.Chain (Chain (..), RoundNumber (..), Vote (..))
import Peras.IOSim.Chain (
  addBlock,
  addChain,
  addVote,
  appendBlock,
  blocksInWindow,
  eligibleDanglingVotes,
  filterDanglingVotes,
  isBlockOnChain,
  lookupBlock,
  lookupRoundForChain,
  lookupVote,
  preferChain,
  resolveBlock,
  resolveBlocksOnChain,
  voteRecorded,
 )
import Peras.IOSim.Chain.Types (ChainState (preferredChain, voteIndex))
import Peras.IOSim.Crypto (VrfOutput, committeMemberRandom, nextVrf, proveLeadership, proveMembership, signBlock, signVote, slotLeaderRandom)
import Peras.IOSim.Hash (hashBlock, hashTip, hashVote)
import Peras.IOSim.Node.Types (NodeState, chainState, committeeMember, nodeId, owner, rollbacks, slot, slotLeader, stake, vrfOutput)
import Peras.IOSim.Protocol.Types (Invalid (..), Protocol (..))
import Peras.IOSim.Types (Coin, Message', Rollback (..), Vote', VoteWithBlock)
import Peras.Message (Message (NewChain, SomeBlock, SomeVote))
import qualified Peras.Message

import qualified Data.Map as M
import qualified Data.Set as S

uses' :: MonadError e m => MonadState s m => Lens' s a -> (a -> Either e b) -> m b
uses' l f = uses l f >>= liftEither

(%#=) :: MonadError e m => MonadState s m => Lens' s a -> (a -> Either e a) -> m ()
l %#= f = uses l f >>= either throwError (l .=)

sayInvalid :: MonadSay m => a -> ExceptT Invalid m a -> m a
sayInvalid d x = runExceptT x >>= either ((>> pure d) . say . show) pure

nextSlot ::
  MonadSay m =>
  MonadState NodeState m =>
  Protocol ->
  Slot ->
  Coin ->
  m [Message']
nextSlot protocol@Peras{..} slotNumber total =
  do
    slot .= slotNumber
    chainState %= discardExpiredVotes protocol slotNumber
    vrfOutput %= nextVrf
    vrf <- use vrfOutput
    leader <- isSlotLeader activeSlotCoefficient total vrf <$> use stake
    slotLeader .= leader
    leaderMessages <-
      if leader
        then doLeading slotNumber vrf
        else pure mempty
    voterMessages <-
      if isFirstSlotInRound protocol slotNumber
        then do
          let r = currentRound protocol slotNumber
          votingAllowed <- chainState `uses` voteInRound protocol r
          voter <- isCommitteeMember pCommitteeLottery total vrf <$> use stake
          committeeMember .= voter
          if voter && votingAllowed
            then doVoting protocol slotNumber r vrf
            else pure mempty
        else pure mempty
    pure $ leaderMessages <> voterMessages

doLeading ::
  MonadSay m =>
  MonadState NodeState m =>
  Slot ->
  VrfOutput ->
  m [Message']
doLeading slotNumber vrf =
  sayInvalid mempty $ do
    block <-
      Block slotNumber
        <$> use owner
        <*> uses chainState (hashTip . Peras.Chain.blocks . preferredChain)
        <*> uses' chainState eligibleDanglingVotes
        <*> pure (proveLeadership vrf ())
        <*> pure mempty
        <*> pure (signBlock vrf ())
    chainState %#= appendBlock block
    -- FIXME: Implement `prefixCutoffWeight` logic.
    chainState `uses` (pure . NewChain . preferredChain)

doVoting ::
  MonadSay m =>
  MonadState NodeState m =>
  Protocol ->
  Slot ->
  RoundNumber ->
  VrfOutput ->
  m [Message']
doVoting protocol slotNumber r vrf =
  sayInvalid mempty $ do
    chainState `uses` (blocksInWindow (candidateWindow protocol slotNumber) . preferredChain)
      >>= \case
        block : _ -> do
          vote <-
            MkVote r
              <$> use owner
              <*> pure (proveMembership vrf ())
              <*> pure (hashBlock block)
              <*> pure (signVote vrf ())
          message <- newBlock' protocol block
          addValidVote protocol vote
          --        pure $ SomeVote vote : message
          pure $ message <> [SomeVote vote]
        [] -> pure mempty

newChain ::
  MonadSay m =>
  MonadState NodeState m =>
  Protocol ->
  Chain ->
  m [Message']
newChain protocol proposed =
  sayInvalid mempty $ do
    fromWeight <- chainState `uses` chainWeight protocol
    notEquivocated <- chainState `uses` (((/= Left EquivocatedVote) .) . checkEquivocation)
    let proposed' = proposed{votes = filter notEquivocated $ votes proposed}
    state' <- chainState `uses'` preferChain proposed'
    -- FIXME: Should the whole chain be rejected if any part of it or the its dangling votes is invalid?
    liftEither $ do
      validChain protocol state'
      mapM_ (validCandidateWindow protocol <=< resolveBlock state') $ votes proposed'
    let toWeight = chainWeight protocol state'
        checkRollback MkChain{blocks = olds} MkChain{blocks = news} =
          partition (`elem` news) olds
            & \case
              (_, []) -> pure ()
              (prefix, suffix) ->
                let
                  atSlot = if null prefix then 0 else slotNumber $ head prefix
                  slots = on (-) fromIntegral (slotNumber $ head suffix) atSlot
                  blocks = fromIntegral $ length suffix
                 in
                  rollbacks %= (Rollback{..} :)
    if toWeight > fromWeight
      then do
        flip checkRollback proposed' =<< chainState `uses` preferredChain
        chainState .= state'
        pure [NewChain proposed']
      else do
        chainState %#= addChain proposed'
        newVotes protocol $ Peras.Chain.votes proposed'

newBlock ::
  MonadSay m =>
  MonadState NodeState m =>
  Protocol ->
  Block ->
  m [Message']
newBlock protocol block =
  sayInvalid mempty $ newBlock protocol block

newBlock' ::
  MonadError Invalid m =>
  MonadState NodeState m =>
  Protocol ->
  Block ->
  m [Message']
newBlock' _ block =
  do
    Peras.Message.MkNodeId z <- use nodeId
    chainState `uses` lookupBlock (trace (z <> " REC " <> show (hashBlock block)) hashBlock block)
      >>= \case
        Right _ -> pure mempty
        Left _ -> do
          chainState %#= addBlock block
          pure [SomeBlock block]

newVote ::
  MonadSay m =>
  MonadState NodeState m =>
  Protocol ->
  Vote' ->
  m [Message']
newVote = (sayInvalid mempty .) . newVote'

newVote' ::
  MonadError Invalid m =>
  MonadState NodeState m =>
  Protocol ->
  Vote' ->
  m [Message']
newVote' protocol vote =
  do
    Peras.Message.MkNodeId z <- use nodeId
    chainState `uses` lookupVote (trace (z <> " REF " <> show (blockHash vote)) hashVote vote)
      >>= \case
        Right _ -> pure mempty
        Left _ -> do
          chainState `uses` lookupBlock (blockHash vote)
            >>= \case
              Right _ -> trace "  FOUND" pure ()
              Left _ -> error "  NOT FOUND"
          addValidVote protocol vote
          pure [SomeVote vote]

newVotes ::
  MonadError Invalid m =>
  MonadState NodeState m =>
  Protocol ->
  [Vote'] ->
  m [Message']
newVotes protocol votes =
  do
    -- FIXME: This results in only the valid votes before the
    --        the first invalid vote.
    concat <$> mapM (newVote' protocol) votes

isSlotLeader ::
  Double ->
  Coin ->
  VrfOutput ->
  Coin ->
  Bool
isSlotLeader activeSlotCoefficient' total vrf staked =
  let p = 1 - (1 - activeSlotCoefficient') ** (fromIntegral staked / fromIntegral total)
   in slotLeaderRandom vrf <= p

isCommitteeMember ::
  Double ->
  Coin ->
  VrfOutput ->
  Coin ->
  Bool
isCommitteeMember pCommitteeLottery' _total vrf staked =
  let p = 1 - (1 - pCommitteeLottery') ^ staked
   in committeMemberRandom vrf <= p

candidateWindow ::
  Protocol ->
  Slot ->
  (Slot, Slot)
candidateWindow Peras{votingWindow} s =
  ( s - min s (fromIntegral $ fst votingWindow)
  , s - min s (fromIntegral $ snd votingWindow)
  )

inclusionWindow ::
  Protocol ->
  Slot ->
  (Slot, Slot)
inclusionWindow Peras{voteMaximumAge} s =
  ( s - min s (fromIntegral voteMaximumAge)
  , s - min s 1
  )

discardExpiredVotes ::
  Protocol ->
  Slot ->
  ChainState ->
  ChainState
discardExpiredVotes protocol@Peras{voteMaximumAge = aa} now =
  filterDanglingVotes $
    \(vote, _) ->
      let
        s = firstSlotInRound protocol $ votingRound vote
       in
        s + 1 <= now && now <= s + aa

addValidVote ::
  MonadError Invalid m =>
  MonadState NodeState m =>
  Protocol ->
  Vote' ->
  m ()
addValidVote protocol vote =
  do
    state <- use chainState
    block <- liftEither $ snd <$> resolveBlock state vote
    liftEither $ do
      checkEquivocation state vote
      validCandidateWindow protocol (vote, block)
    state' <- liftEither $ addVote (vote, block) state
    chainState .= state'

checkEquivocation ::
  ChainState ->
  Vote' ->
  Either Invalid ()
checkEquivocation state vote =
  let
    equivocation vote' =
      votingRound vote == votingRound vote'
        && creatorId vote == creatorId vote'
        && signature vote /= signature vote'
   in
    unless (M.null . M.filter equivocation $ voteIndex state) $
      throwError EquivocatedVote

-- | "A chain is *valid* if the blocks form a *valid Praos chain* and each vote
--   is valid."
validChain :: Protocol -> ChainState -> Either Invalid ()
validChain protocol state =
  do
    validPraos (preferredChain state)
    blocks <- resolveBlocksOnChain state
    forM_ blocks $ validVote protocol state

-- | Check whether a chain is valid Praos.
validPraos :: Chain -> Either Invalid ()
validPraos MkChain{blocks = []} = pure ()
validPraos MkChain{blocks} =
  -- FIXME: Also check signatures and proofs.
  unless (and $ zipWith ((>) `on` slotNumber) (init blocks) (tail blocks)) $
    throwError InvalidPraosChain

-- | A valid vote votes for a block whose slot is in the vote-candidate window
--   and if it is referenced by a unique block in the vote-inclusion window.
validVote :: Protocol -> ChainState -> VoteWithBlock -> Either Invalid ()
validVote protocol state (vote, block) =
  do
    -- FIXME: Also check signatures and proofs.
    validCandidate protocol state (vote, block)
    validInclusion protocol state vote
    voteAllowedInRound protocol state vote

-- | "Each vote $v$, with some slot number $s = r * T$, votes for a block with
--   slot number in the *voting-candidate window* $\[s - L_low, s - L_high\]$
--   *on the chain*.
validCandidate :: Protocol -> ChainState -> VoteWithBlock -> Either Invalid ()
validCandidate protocol state (vote, block) =
  if isBlockOnChain state (hashBlock block)
    then validCandidateWindow protocol (vote, block)
    else throwError VoteNeverRecorded

validCandidateWindow :: Protocol -> VoteWithBlock -> Either Invalid ()
validCandidateWindow protocol@Peras{votingWindow = (lLow, lHigh)} (MkVote{votingRound = r}, Block{slotNumber}) =
  let
    s = firstSlotInRound protocol r
   in
    unless (s <= slotNumber + lLow && slotNumber + lHigh <= s) $
      throwError VoteOutsideCandidateWindow

-- | "Each vote $v$, with some slot number $s = r * T$, is *referenced by a
--   unique block* with a slot number s inside the *vote-inclusions window*
--   $\[s + 1, s + A\]$."
validInclusion :: Protocol -> ChainState -> Vote' -> Either Invalid ()
validInclusion protocol@Peras{voteMaximumAge = aa} state vote@MkVote{votingRound = r} =
  let
    s = firstSlotInRound protocol r
   in
    -- FIXME: Use `ChainState` to make this more efficient.
    case voteRecorded (preferredChain state) vote of
      [Block{slotNumber}] ->
        unless (s + 1 <= slotNumber && slotNumber <= s + aa) $
          throwError VoteOutsideInclusionWindow
      [] -> throwError VoteNeverRecorded
      _ -> throwError VoteRecordedMultipleTimes

voteAllowedInRound :: Protocol -> ChainState -> Vote msg -> Either Invalid ()
voteAllowedInRound protocol state MkVote{votingRound} =
  unless (voteInRound protocol votingRound state) $
    throwError VoteNotAllowedInRound

currentRound :: Protocol -> Slot -> RoundNumber
currentRound Peras{roundDuration = tt} s = MkRoundNumber $ s `div` tt

firstSlotInRound :: Protocol -> RoundNumber -> Slot
firstSlotInRound Peras{roundDuration = tt} MkRoundNumber{roundNumber = r} = r * tt

isFirstSlotInRound :: Protocol -> Slot -> Bool
isFirstSlotInRound Peras{roundDuration = tt} s = s `mod` tt == 0

chainWeight :: Protocol -> ChainState -> Double
chainWeight protocol state =
  let
    chain@MkChain{blocks} = preferredChain state
    s = if null blocks then 0 else slotNumber (head blocks)
    rCurrent = currentRound protocol s
    w0 = length blocks
    w' =
      sum
        [ sum $ S.size <$> M.elems vs
        | r <- [0 .. rCurrent]
        , voteInRound protocol r state
        , let vs = lookupRoundForChain r state chain
        ]
   in
    fromIntegral w0
      + votingBoost protocol * fromIntegral w'

-- FIXME: The ellipsis in pseudo-code specification likely is incorrect.
voteInRound :: Protocol -> RoundNumber -> ChainState -> Bool
voteInRound _ (MkRoundNumber 0) _ = False
voteInRound protocol (MkRoundNumber r) state =
  let
    kk = toInteger $ cooldownDuration protocol
    quorum = quorumOnChain protocol state . MkRoundNumber . fromIntegral
    condition r' = quorum r' && not (quorum $ r' + 1)
   in
    quorum (toInteger r - 1)
      || any condition [toInteger r - kk, toInteger r - 2 * kk .. 0]

-- | "Predicate `quorumOnChain`$(C, D, r)$ checks whether this is a round-$r$
--   *quorum* in $C$ and $D$ for a block on $C$: "a *quorum*, which consists of
--   *at least $\tau$ round-$r$ votes for the *same message*."
quorumOnChain :: Protocol -> ChainState -> RoundNumber -> Bool
quorumOnChain _ _ 0 = True -- FIXME: The initial quorum can never be established without this.
quorumOnChain Peras{votingQuorum = tau} state r =
  any ((>= tau) . S.size) . M.elems $
    lookupRoundForChain r state (preferredChain state)
