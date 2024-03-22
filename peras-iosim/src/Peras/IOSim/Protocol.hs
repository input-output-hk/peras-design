{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}

module Peras.IOSim.Protocol (
  candidateWindow,
  chainWeight,
  checkEquivocation,
  currentRound,
  discardExpiredVotes,
  firstSlotInRound,
  inclusionWindow,
  isCommitteeMember,
  isSlotLeader,
  isFirstSlotInRound,
  quorumOnChain,
  roundNumber,
  validCandidate,
  validCandidateWindow,
  validChain,
  validInclusion,
  validPraos,
  validVote,
  voteInRound,
) where

import Control.Monad (forM_, unless)
import Control.Monad.Except (MonadError (throwError))
import Data.Function (on)
import Peras.Block (Block (Block, slotNumber), Slot)
import Peras.Chain (Chain, RoundNumber (..), Vote (..))
import Peras.IOSim.Chain (
  filterDanglingVotes,
  isBlockOnChain,
  lookupRoundForChain,
  resolveBlocksOnChain,
 )
import Peras.IOSim.Chain.Types (ChainState (preferredChain, voteIndex))
import Peras.IOSim.Crypto (VrfOutput, committeMemberRandom, slotLeaderRandom)
import Peras.IOSim.Hash (hashBlock)
import Peras.IOSim.Protocol.Types (Invalid (..), Protocol (..))
import Peras.IOSim.Types (Coin, VoteWithBlock)

import qualified Data.Map as M
import qualified Data.Set as S

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
  -- FIXME: This isn't faithful to the "Settle It Already" document,
  --        which implies that one block-producer can have several
  --        votes on the committee.
  let p = 1 - (1 - pCommitteeLottery') ^ staked
   in committeMemberRandom vrf <= p

candidateWindow ::
  Protocol ->
  Slot ->
  (Slot, Slot)
candidateWindow Peras{votingWindow} s =
  ( s - min s (fst votingWindow)
  , s - min s (snd votingWindow)
  )

inclusionWindow ::
  Protocol ->
  Slot ->
  (Slot, Slot)
inclusionWindow Peras{voteMaximumAge} s =
  ( s - min s voteMaximumAge
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

checkEquivocation ::
  ChainState ->
  Vote ->
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
validPraos [] = pure ()
validPraos blocks =
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
validInclusion :: Protocol -> ChainState -> Vote -> Either Invalid ()
validInclusion _ _ _ =
  -- FIXME: Currently it is impossible to verify that a vote was included in a certificate.
  pure ()

voteAllowedInRound :: Protocol -> ChainState -> Vote -> Either Invalid ()
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
    blocks = preferredChain state
    s = if null blocks then 0 else slotNumber (head blocks)
    rCurrent = currentRound protocol s
    w0 = length blocks
    w' =
      sum
        [ sum $ S.size <$> M.elems vs
        | r <- [0 .. rCurrent]
        , voteInRound protocol r state
        , let vs = lookupRoundForChain r state blocks
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
