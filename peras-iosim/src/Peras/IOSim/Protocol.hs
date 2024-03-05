{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Protocol (
  newChain,
  nextSlot,
  candidateWindow,
  inclusionWindow,
  roundNumber,
  newVote,
  validChain,
  validPraos,
  validVote,
  validCandidate,
  validInclusion,
  quorumOnChain,
  voteInRound,
  chainWeight,
  isFirstSlotInRound,
  firstSlotInRound,
  currentRound,
) where

import Control.Lens (use, uses, (%=), (&), (.=))
import Control.Monad (replicateM)
import Control.Monad.Random (MonadRandom (getRandom, getRandomR))
import Control.Monad.State (MonadState)
import Data.Function (on)
import Data.List (partition)
import Numeric.Natural (Natural)
import Peras.Block (Block (Block, slotNumber), Slot)
import Peras.Chain (Chain (..), RoundNumber (..), Vote (..))
import Peras.Crypto (LeadershipProof (LeadershipProof), MembershipProof (MembershipProof), Signature (Signature))
import Peras.IOSim.Chain (
  ChainState (preferredChain),
  addChain,
  addVote,
  appendBlock,
  blocksInWindow,
  eligibleDanglingVotes,
  filterDanglingVotes,
  isBlockOnChain,
  lookupRoundForChain,
  lookupVote,
  preferChain,
  resolveBlock,
  resolveBlocksOnChain,
  voteRecorded,
 )
import Peras.IOSim.Hash (hashBlock, hashTip, hashVote)
import Peras.IOSim.Node.Types (NodeState, chainState, committeeMember, owner, rollbacks, slot, slotLeader, stake, vrfOutput)
import Peras.IOSim.Protocol.Types (Protocol (..))
import Peras.IOSim.Types (Coin, Message', Rollback (..), Vote')
import Peras.Message (Message (NewChain, SomeVote))

import qualified Data.ByteString as BS
import qualified Data.Map as M
import qualified Data.Set as S

nextSlot ::
  MonadRandom m =>
  MonadState NodeState m =>
  Protocol ->
  Slot ->
  Coin ->
  m [Message']
nextSlot protocol@Peras{..} slotNumber total =
  do
    -- FIXME: Improve handling of incomplete indexes.
    let handleIncompleteIndex = either (error . show) id
    slot .= slotNumber
    chainState %= discardExpiredVotes protocol slotNumber
    vrf <- getRandomR (0, 1)
    vrfOutput .= vrf
    leader <- isSlotLeader activeSlotCoefficient total (uniformRandomFromVrf vrf 0) <$> use stake
    slotLeader .= leader
    leaderMessages <-
      if leader
        then do
          block <-
            Block slotNumber
              <$> use owner
              <*> uses chainState (hashTip . Peras.Chain.blocks . preferredChain)
              <*> uses chainState (handleIncompleteIndex . eligibleDanglingVotes)
              <*> (LeadershipProof . BS.pack <$> replicateM 6 getRandom)
              <*> pure mempty
              <*> (Signature . BS.pack <$> replicateM 6 getRandom)
          chainState %= handleIncompleteIndex . appendBlock block
          -- FIXME: Implement `prefixCutoffWeight` logic.
          chainState `uses` (pure . NewChain . preferredChain)
        else pure mempty
    voterMessages <-
      if isFirstSlotInRound protocol slotNumber
        then do
          let r = currentRound protocol slotNumber
          votingAllowed <- chainState `uses` voteInRound protocol r
          voter <- isCommitteeMember pCommitteeLottery total (uniformRandomFromVrf vrf 1) <$> use stake
          committeeMember .= voter
          if voter && votingAllowed
            then do
              chainState `uses` (blocksInWindow (candidateWindow protocol slotNumber) . preferredChain)
                >>= \case
                  block : _ -> do
                    vote <-
                      MkVote r
                        <$> use owner
                        <*> (MembershipProof . BS.pack <$> replicateM 6 getRandom)
                        <*> pure block
                        <*> (Signature . BS.pack <$> replicateM 6 getRandom)
                    chainState %= handleIncompleteIndex . addVote vote
                    pure [SomeVote vote]
                  [] -> pure mempty
            else pure mempty
        else pure mempty
    pure $ leaderMessages <> voterMessages

newChain ::
  MonadState NodeState m =>
  Protocol ->
  Chain ->
  m [Message']
newChain protocol proposed =
  do
    -- FIXME: Improve handling of incomplete indexes.
    let handleIncompleteIndex = either (error . show) id
    fromWeight <- chainState `uses` chainWeight protocol
    state' <- chainState `uses` (handleIncompleteIndex . preferChain proposed)
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
        flip checkRollback proposed =<< chainState `uses` preferredChain
        chainState .= state'
        pure [NewChain proposed]
      else do
        chainState %= handleIncompleteIndex . addChain proposed
        newVotes $ Peras.Chain.votes proposed

newVote ::
  MonadState NodeState m =>
  Vote Block ->
  m [Message']
newVote vote =
  do
    -- FIXME: Improve handling of incomplete indexes.
    let handleIncompleteIndex = either (error . show) id
    chainState `uses` lookupVote (hashVote vote)
      >>= \case
        Right _ -> pure mempty
        Left _ -> do
          chainState %= handleIncompleteIndex . addVote vote
          pure [SomeVote vote]

newVotes ::
  MonadState NodeState m =>
  [Vote'] ->
  m [Message']
newVotes votes =
  do
    -- FIXME: Improve handling of incomplete indexes.
    let handleIncompleteIndex = either (error . show) id
    state <- use chainState
    let votes' = handleIncompleteIndex $ mapM (resolveBlock state) votes
    concat <$> mapM newVote votes'

uniformRandomFromVrf ::
  Double ->
  Natural ->
  Double
uniformRandomFromVrf vrf index =
  let
    b = 10
    x = b ^ index * vrf
   in
    x - fromIntegral (floor x :: Integer)

isSlotLeader ::
  Double ->
  Coin ->
  Double ->
  Coin ->
  Bool
isSlotLeader activeSlotCoefficient' total uniformRandom staked =
  let p = 1 - (1 - activeSlotCoefficient') ** (fromIntegral staked / fromIntegral total)
   in uniformRandom <= p

isCommitteeMember ::
  Double ->
  Coin ->
  Double ->
  Coin ->
  Bool
isCommitteeMember pCommitteeLottery' _total uniformRandom staked =
  let p = 1 - (1 - pCommitteeLottery') ^ staked
   in uniformRandom <= p

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
    \vote ->
      let
        s = firstSlotInRound protocol $ votingRound vote
       in
        s + 1 <= now && now <= s + aa

-- | "A chain is *valid* if the blocks form a *valid Praos chain* and each vote
--   is valid."
validChain :: Protocol -> ChainState -> Bool
validChain protocol state =
  validPraos (preferredChain state)
    && either (const False) (all $ validVote protocol state) (resolveBlocksOnChain state)

-- | Check whether a chain is valid Praos.
validPraos :: Chain -> Bool
validPraos MkChain{blocks = []} = True
validPraos MkChain{blocks} =
  -- FIXME: Also check signatures and proofs.
  and $ zipWith ((>) `on` slotNumber) (init blocks) (tail blocks)

-- | A valid vote votes for a block whose slot is in the vote-candidate window
--   and if it is referenced by a unique block in the vote-inclusion window.
validVote :: Protocol -> ChainState -> Vote Block -> Bool
validVote protocol state vote =
  -- FIXME: Also check signatures and proofs.
  validCandidate protocol state vote && validInclusion protocol state vote

-- | "Each vote $v$, with some slot number $s = r * T$, votes for a block with
--   slot number in the *voting-candidate window* $\[s - L_low, s - L_high\]$
--   *on the chain*.
validCandidate :: Protocol -> ChainState -> Vote Block -> Bool
validCandidate protocol@Peras{votingWindow = (lLow, lHigh)} state MkVote{votingRound = r, blockHash = block@Block{slotNumber}} =
  let
    s = firstSlotInRound protocol r
   in
    isBlockOnChain state (hashBlock block) && s <= slotNumber + lLow && slotNumber + lHigh <= s

-- | "Each vote $v$, with some slot number $s = r * T$, is *referenced by a
--   unique block* with a slot number s inside the *vote-inclusions window*
--   $\[s + 1, s + A\]$."
validInclusion :: Protocol -> ChainState -> Vote msg -> Bool
validInclusion protocol@Peras{voteMaximumAge = aa} state vote@MkVote{votingRound = r} =
  let
    s = firstSlotInRound protocol r
   in
    -- FIXME: Use `ChainState` to make this more efficient.
    case voteRecorded (preferredChain state) vote of
      [Block{slotNumber}] -> s + 1 <= slotNumber && slotNumber <= s + aa
      _ -> False

currentRound :: Protocol -> Slot -> RoundNumber
currentRound Peras{roundDuration = tt} s = RoundNumber $ s `div` tt

firstSlotInRound :: Protocol -> RoundNumber -> Slot
firstSlotInRound Peras{roundDuration = tt} RoundNumber{roundNumber = r} = r * tt

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
voteInRound _ (RoundNumber 0) _ = False
voteInRound protocol (RoundNumber r) state =
  let
    kk = toInteger $ cooldownDuration protocol
    quorum = quorumOnChain protocol state . RoundNumber . fromIntegral
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
