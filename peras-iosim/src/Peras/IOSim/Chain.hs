{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Chain (
  addChain,
  preferChain,
  lookupVote,
  lookupVote',
  lookupBlock,
  lookupRound,
  lookupRoundForChain,
  blocksInWindow,
  blockInWindow,
  voteOnChain,
  voteOnChain',
  Invalid (..),
  voteRecorded,
  blockOnChain,
  resolveBlock,
  resolveBlocksOnChain,
  votesRecordedOnChain,
  votesRecordedOnChain',
  votesForBlocksOnChain,
  votesForBlocksOnChain',
  indexChain,
  filterDanglingVotes,
  filterVotesByRound,
  isBlockOnChain,
  isVoteRecordedOnChain,
  eligibleDanglingVotes,
  appendBlock,
  addBlock,
  addVote,
) where

import Control.Monad (filterM, unless, (<=<))
import Control.Monad.Except (throwError)
import Data.Default (Default (def))
import Data.Foldable (foldr')
import Data.Maybe (fromMaybe)
import Peras.Block (Block (..), Slot)
import Peras.Chain (Chain (..), RoundNumber, Vote (..))
import Peras.IOSim.Chain.Types (ChainState (..))
import Peras.IOSim.Hash (BlockHash, VoteHash, hashBlock, hashVote)
import Peras.IOSim.Protocol.Types (Invalid (..))
import Peras.IOSim.Types (Vote')
import Peras.Orphans ()

import qualified Data.Map as M
import qualified Data.Set as S

indexChain :: Chain -> Either Invalid ChainState
indexChain = flip preferChain def

preferChain :: Chain -> ChainState -> Either Invalid ChainState
preferChain chain state =
  do
    state' <- addChain chain state
    pure
      state'
        { preferredChain = chain
        , danglingBlocks = M.keysSet (blockIndex state') `S.difference` S.fromList (hashBlock <$> blocks chain)
        , danglingVotes = M.keysSet (voteIndex state') `S.difference` S.fromList (concatMap includedVotes $ blocks chain)
        }

appendBlock :: Block -> ChainState -> Either Invalid ChainState
appendBlock block state =
  do
    votes' <- mapM (`lookupVote'` state) $ includedVotes block
    pure
      state
        { preferredChain =
            MkChain
              { blocks = block : blocks (preferredChain state)
              , votes = votes' <> votes (preferredChain state) -- We don't need to guard against duplicates here.
              }
        , blockIndex = M.insert (hashBlock block) block $ blockIndex state
        , danglingVotes = danglingVotes state `S.difference` S.fromList (includedVotes block)
        }

addChain :: Chain -> ChainState -> Either Invalid ChainState
addChain MkChain{..} state =
  do
    let
      indexBlock block = M.insert (hashBlock block) block
      indexVote vote = M.insert (hashVote vote) vote
      indexRound v =
        M.insertWith
          (M.unionWith S.union)
          (votingRound v)
          (M.singleton (blockHash v) (S.singleton $ hashVote v))
      state' =
        state
          { blockIndex = foldr' indexBlock (blockIndex state) blocks
          , voteIndex = foldr' indexVote (voteIndex state) votes
          , votesByRound = foldr' indexRound (votesByRound state) votes
          }
      blockReferencesOkay = all ((`M.member` blockIndex state') . blockHash) votes
      voteReferencesOkay = all (all (`M.member` voteIndex state') . includedVotes) blocks
    unless blockReferencesOkay $
      throwError VoteReferencesUnknownBlock
    unless voteReferencesOkay $
      throwError BlockIncludesUnknownVote
    pure state'

addBlock :: Block -> ChainState -> Either Invalid ChainState
addBlock block state =
  let
    bhash = hashBlock block
   in
    if bhash `M.member` blockIndex state
      then pure state
      else do
        mapM_ (`lookupVote'` state) $ includedVotes block
        pure
          state
            { blockIndex = M.insert (hashBlock block) block $ blockIndex state
            , danglingBlocks =
                (if bhash `elem` fmap hashBlock (blocks $ preferredChain state) then id else S.insert bhash) $
                  danglingBlocks state
            }

addVote :: Vote Block -> ChainState -> Either Invalid ChainState
addVote vote state =
  if hashVote vote `M.member` voteIndex state
    then pure state
    else
      let
        block = blockHash vote
        bhash = hashBlock block
        vote' = vote{blockHash = bhash}
        vhash = hashVote vote'
        r = votingRound vote
       in
        pure
          state
            { blockIndex = M.insert (hashBlock block) block $ blockIndex state
            , voteIndex = M.insert vhash vote' $ voteIndex state
            , danglingBlocks =
                (if bhash `elem` fmap hashBlock (blocks $ preferredChain state) then id else S.insert bhash) $
                  danglingBlocks state
            , danglingVotes = S.insert vhash $ danglingVotes state
            , votesByRound = M.insertWith M.union r (M.singleton bhash $ S.singleton vhash) $ votesByRound state
            }

lookupBlock :: BlockHash -> ChainState -> Either Invalid Block
lookupBlock hash ChainState{blockIndex} =
  maybe (throwError HashOfUnknownBlock) pure $
    hash `M.lookup` blockIndex

lookupVote :: VoteHash -> ChainState -> Either Invalid (Vote Block)
lookupVote hash state = resolveBlock state =<< hash `lookupVote'` state

lookupVote' :: VoteHash -> ChainState -> Either Invalid Vote'
lookupVote' hash ChainState{voteIndex} =
  maybe (throwError HashOfUnknownVote) pure $
    hash `M.lookup` voteIndex

lookupRound :: RoundNumber -> ChainState -> M.Map BlockHash (S.Set VoteHash)
lookupRound r state = fromMaybe mempty $ r `M.lookup` votesByRound state

lookupRoundForChain :: RoundNumber -> ChainState -> Chain -> M.Map BlockHash (S.Set VoteHash)
lookupRoundForChain r state chain =
  M.restrictKeys
    (r `lookupRound` state)
    (S.fromList $ hashBlock <$> blocks chain)

isBlockOnChain :: ChainState -> BlockHash -> Bool
isBlockOnChain = flip S.notMember . danglingBlocks

isVoteRecordedOnChain :: ChainState -> VoteHash -> Bool
isVoteRecordedOnChain = flip S.notMember . danglingVotes

resolveBlock :: ChainState -> Vote' -> Either Invalid (Vote Block)
resolveBlock state vote =
  do
    block <- blockHash vote `lookupBlock` state
    pure vote{blockHash = block}

resolveBlocksOnChain :: ChainState -> Either Invalid [Vote Block]
resolveBlocksOnChain state =
  mapM (resolveBlock state) . M.elems $
    M.withoutKeys (voteIndex state) (danglingVotes state)

votesRecordedOnChain :: Chain -> Either Invalid [Vote Block]
votesRecordedOnChain = resolveBlocksOnChain <=< indexChain

votesRecordedOnChain' :: Chain -> Either Invalid [Vote']
votesRecordedOnChain' chain =
  do
    state <- indexChain chain
    pure . M.elems $
      M.withoutKeys (voteIndex state) (danglingVotes state)

votesForBlocksOnChain :: Chain -> Either Invalid [Vote Block]
votesForBlocksOnChain chain =
  do
    state <- indexChain chain
    let hashes = M.keysSet (blockIndex state) `S.difference` danglingBlocks state
    mapM (resolveBlock state) . M.elems $
      M.filter ((`S.member` hashes) . blockHash) (voteIndex state)

votesForBlocksOnChain' :: Chain -> Either Invalid [Vote']
votesForBlocksOnChain' chain =
  do
    state <- indexChain chain
    let hashes = M.keysSet (blockIndex state) `S.difference` danglingBlocks state
    pure . M.elems $
      M.filter ((`S.member` hashes) . blockHash) (voteIndex state)

eligibleDanglingVotes :: ChainState -> Either Invalid [VoteHash]
eligibleDanglingVotes state =
  do
    let hashes = M.keysSet (blockIndex state) `S.difference` danglingBlocks state
    filterM (fmap (flip S.member hashes . blockHash) . flip lookupVote' state)
      . S.toList
      $ danglingVotes state

filterDanglingVotes :: (Vote Block -> Bool) -> ChainState -> ChainState
filterDanglingVotes f state =
  state
    { danglingVotes = S.filter (either (const False) f . flip lookupVote state) $ danglingVotes state
    }

filterVotesByRound :: (Vote Block -> Bool) -> ChainState -> ChainState
filterVotesByRound f state =
  state
    { votesByRound = M.map (M.map $ S.filter (either (const False) f . flip lookupVote state)) $ votesByRound state
    }

blockInWindow :: (Slot, Slot) -> Block -> Bool
blockInWindow (oldest, newest) Block{slotNumber} = oldest <= slotNumber && slotNumber <= newest

blocksInWindow :: (Slot, Slot) -> Chain -> [Block]
blocksInWindow window = filter (blockInWindow window) . blocks

voteOnChain :: Chain -> Vote Block -> Bool
voteOnChain MkChain{blocks} MkVote{blockHash} = any ((== hashBlock blockHash) . hashBlock) blocks

voteOnChain' :: Chain -> Vote' -> Bool
voteOnChain' MkChain{blocks} MkVote{blockHash} = any ((== blockHash) . hashBlock) blocks

blockOnChain :: Chain -> Block -> Bool
blockOnChain MkChain{blocks} block = any ((== hashBlock block) . hashBlock) blocks

voteRecorded :: Chain -> Vote msg -> [Block]
voteRecorded MkChain{blocks} vote = filter ((hashVote vote `elem`) . includedVotes) blocks
