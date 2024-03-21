{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

module Peras.IOSim.Chain (
  Invalid (..),
  addBlock,
  addBody,
  addChain,
  addVote,
  appendBlock,
  blockTree,
  blockTrees,
  blocksInWindow,
  blocksMissingFromChain,
  buildChain,
  eligibleDanglingVotes,
  filterDanglingVotes,
  isBlockOnChain,
  lookupBlock,
  lookupBody,
  lookupRoundForChain,
  lookupVote,
  missingBlocks,
  missingIncludedVotes,
  missingParents,
  missingVotedBlocks,
  missingVotes,
  preferChain,
  resolveBlock,
  resolveBlocksOnChain,
  voteRecorded,
  votesMissingFromChain,
) where

import Control.Monad.Except (throwError)
import Data.Default (Default (def))
import Data.Either (rights)
import Data.Foldable (foldr')
import Data.List (nub)
import Data.Maybe (fromMaybe, mapMaybe)
import Peras.Block (Block (..), BlockBody, Slot)
import Peras.Chain (Chain (..), RoundNumber, Vote (..))
import Peras.IOSim.Chain.Types (BlockTree, ChainState (..))
import Peras.IOSim.Hash (BlockHash, BodyHash, VoteHash, genesisHash, hashBlock, hashBody, hashVote)
import Peras.IOSim.Protocol.Types (Invalid (..))
import Peras.IOSim.Types (VoteWithBlock)
import Peras.Orphans ()

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Tree as T

blockTrees :: [ChainState] -> BlockTree
blockTrees states =
  let
    index = M.unions $ blockIndex <$> states
    edges = M.foldr (\block -> M.insertWith S.union (parentBlock block) $ S.singleton block) def index
    children hash =
      (index M.! hash,)
        . maybe mempty (fmap hashBlock . S.toList)
        $ hash `M.lookup` edges
    roots = snd $ children genesisHash
   in
    T.unfoldForest children roots

blockTree :: ChainState -> BlockTree
blockTree = blockTrees . pure

preferChain :: Chain -> ChainState -> ChainState
preferChain chain state =
  let state' = addChain chain state
   in state'
        { preferredChain = chain
        , danglingBlocks = M.keysSet (blockIndex state') `S.difference` S.fromList (hashBlock <$> blocks chain)
        , danglingVotes = M.keysSet (voteIndex state') `S.difference` S.fromList (concatMap includedVotes $ blocks chain)
        }

appendBlock :: Block -> ChainState -> ChainState
appendBlock block state =
  let votes' = rights $ (`lookupVote'` state) <$> includedVotes block
   in state
        { preferredChain =
            MkChain
              { blocks = block : blocks (preferredChain state)
              , votes = nub $ votes' <> votes (preferredChain state)
              }
        , blockIndex = M.insert (hashBlock block) block $ blockIndex state
        , danglingVotes = danglingVotes state `S.difference` S.fromList (includedVotes block)
        }

-- Ordered in decreasing age.
missingParents :: [Block] -> ChainState -> [BlockHash]
missingParents blocks ChainState{blockIndex} =
  reverse . filter (`M.notMember` blockIndex) $
    parentBlock <$> blocks

-- Ordered in decreasing age.
missingVotedBlocks :: [Vote] -> ChainState -> [BlockHash]
missingVotedBlocks votes ChainState{blockIndex} =
  reverse . filter (`M.notMember` blockIndex) $
    blockHash <$> votes

-- Ordered in decreasing age.
missingIncludedVotes :: [Block] -> ChainState -> [VoteHash]
missingIncludedVotes blocks ChainState{voteIndex} =
  reverse . concatMap (filter (`M.notMember` voteIndex) . includedVotes) $
    blocks

blocksMissingFromChain :: Chain -> ChainState -> [BlockHash]
blocksMissingFromChain MkChain{..} state =
  nub $
    missingParents blocks state
      <> missingVotedBlocks votes state

votesMissingFromChain :: Chain -> ChainState -> [VoteHash]
votesMissingFromChain = missingIncludedVotes . blocks

missingBlocks :: ChainState -> [BlockHash]
missingBlocks state@ChainState{preferredChain} = blocksMissingFromChain preferredChain state

missingVotes :: ChainState -> [VoteHash]
missingVotes state@ChainState{preferredChain} = votesMissingFromChain preferredChain state

addChain :: Chain -> ChainState -> ChainState
addChain MkChain{..} state =
  let
    indexBlock block = M.insert (hashBlock block) block
    indexVote vote = M.insert (hashVote vote) vote
    indexRound v =
      M.insertWith
        (M.unionWith S.union)
        (votingRound v)
        (M.singleton (blockHash v) (S.singleton $ hashVote v))
   in
    state
      { blockIndex = foldr' indexBlock (blockIndex state) blocks
      , voteIndex = foldr' indexVote (voteIndex state) votes
      , votesByRound = foldr' indexRound (votesByRound state) votes
      }

addBlock :: Block -> ChainState -> ChainState
addBlock block state =
  let
    bhash = hashBlock block
   in
    if bhash `M.member` blockIndex state
      then state
      else do
        state
          { blockIndex = M.insert (hashBlock block) block $ blockIndex state
          , danglingBlocks =
              (if bhash `elem` fmap hashBlock (blocks $ preferredChain state) then id else S.insert bhash) $
                danglingBlocks state
          }

addVote :: Vote -> ChainState -> ChainState
addVote vote state =
  let
    vhash = hashVote vote
    bhash = blockHash vote
    r = votingRound vote
   in
    if vhash `M.member` voteIndex state
      then state
      else
        state
          { voteIndex = M.insert vhash vote $ voteIndex state
          , danglingBlocks =
              (if bhash `elem` fmap hashBlock (blocks $ preferredChain state) then id else S.insert bhash) $
                danglingBlocks state
          , danglingVotes = S.insert vhash $ danglingVotes state
          , votesByRound = M.insertWith M.union r (M.singleton bhash $ S.singleton vhash) $ votesByRound state
          }

addBody :: BlockBody -> ChainState -> ChainState
addBody body state =
  let
    bhash = hashBody body
   in
    if bhash `M.member` blockIndex state
      then state{bodyIndex = M.insert bhash body $ bodyIndex state}
      else state

lookupBlock :: BlockHash -> ChainState -> Either Invalid Block
lookupBlock hash ChainState{blockIndex} =
  maybe (throwError HashOfUnknownBlock) pure $
    hash `M.lookup` blockIndex

lookupVote :: VoteHash -> ChainState -> Either Invalid VoteWithBlock
lookupVote hash state = resolveBlock state =<< hash `lookupVote'` state

lookupVote' :: VoteHash -> ChainState -> Either Invalid Vote
lookupVote' hash ChainState{voteIndex} =
  maybe (throwError HashOfUnknownVote) pure $
    hash `M.lookup` voteIndex

lookupBody :: BodyHash -> ChainState -> Either Invalid BlockBody
lookupBody hash ChainState{bodyIndex} =
  maybe (throwError HashOfUnknownBlock) pure $
    hash `M.lookup` bodyIndex

lookupRound :: RoundNumber -> ChainState -> M.Map BlockHash (S.Set VoteHash)
lookupRound r state = fromMaybe mempty $ r `M.lookup` votesByRound state

lookupRoundForChain :: RoundNumber -> ChainState -> Chain -> M.Map BlockHash (S.Set VoteHash)
lookupRoundForChain r state chain =
  M.restrictKeys
    (r `lookupRound` state)
    (S.fromList $ hashBlock <$> blocks chain)

isBlockOnChain :: ChainState -> BlockHash -> Bool
isBlockOnChain = flip S.notMember . danglingBlocks

resolveBlock :: ChainState -> Vote -> Either Invalid VoteWithBlock
resolveBlock state vote =
  do
    block <- blockHash vote `lookupBlock` state
    pure (vote, block)

resolveBlocksOnChain :: ChainState -> Either Invalid [VoteWithBlock]
resolveBlocksOnChain state =
  mapM (resolveBlock state) . M.elems $
    M.withoutKeys (voteIndex state) (danglingVotes state)

eligibleDanglingVotes :: ChainState -> [VoteHash]
eligibleDanglingVotes state =
  do
    let hashes = M.keysSet (blockIndex state) `S.difference` danglingBlocks state
    filter ((== Right True) . fmap (flip S.member hashes . blockHash) . flip lookupVote' state)
      . S.toList
      $ danglingVotes state

filterDanglingVotes :: (VoteWithBlock -> Bool) -> ChainState -> ChainState
filterDanglingVotes f state =
  state
    { danglingVotes = S.filter (either (const False) f . flip lookupVote state) $ danglingVotes state
    }

blockInWindow :: (Slot, Slot) -> Block -> Bool
blockInWindow (oldest, newest) Block{slotNumber} = oldest <= slotNumber && slotNumber <= newest

blocksInWindow :: (Slot, Slot) -> Chain -> [Block]
blocksInWindow window = filter (blockInWindow window) . blocks

voteRecorded :: Chain -> Vote -> [Block]
voteRecorded MkChain{blocks} vote = filter ((hashVote vote `elem`) . includedVotes) blocks

buildChain :: Block -> ChainState -> Either ([BlockHash], [VoteHash]) Chain
buildChain block ChainState{blockIndex, voteIndex} =
  let
    buildChain' block'@Block{parentBlock, includedVotes} (blocksFound, votesFound, blocksMissing, votesMissing)
      | parentBlock == genesisHash = (blocksFound', votesFound', blocksMissing, votesMissing')
      | otherwise = case parentBlock `M.lookup` blockIndex of
          Just block'' -> buildChain' block'' (blocksFound', votesFound', blocksMissing, votesMissing')
          Nothing -> (blocksFound', votesFound', pure parentBlock, votesMissing')
     where
      blocksFound' = block' : blocksFound
      votesFound' = mapMaybe (`M.lookup` voteIndex) includedVotes <> votesFound
      votesMissing' = filter (`M.notMember` voteIndex) includedVotes <> votesMissing
   in
    case buildChain' block mempty of
      (blocksFound, votesFound, [], []) -> Right $ MkChain (reverse blocksFound) (nub votesFound)
      (_, _, blocksMissing, votesMissing) -> Left (blocksMissing, nub votesMissing)
