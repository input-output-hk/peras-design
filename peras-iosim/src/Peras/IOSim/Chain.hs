{-# LANGUAGE NamedFieldPuns #-}
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
  missingParents,
  missingVotedBlocks,
  preferChain,
  resolveBlock,
  resolveBlocksOnChain,
) where

import Control.Monad.Except (throwError)
import Data.Default (Default (def))
import Data.Foldable (foldr')
import Data.List (nub)
import Data.Maybe (fromMaybe)
import Peras.Block (Block (..), BlockBody)
import Peras.Chain (Chain, Vote (..))
import Peras.IOSim.Chain.Types (BlockTree, ChainState (..))
import Peras.IOSim.Hash (BlockHash, BodyHash, VoteHash, genesisHash, hashBlock, hashBody, hashVote)
import Peras.IOSim.Protocol.Types (Invalid (..))
import Peras.IOSim.Types (VoteWithBlock)
import Peras.Numbering (RoundNumber, SlotNumber)
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
preferChain blocks state =
  let state' = addChain blocks state
   in state'
        { preferredChain = blocks
        , danglingBlocks = M.keysSet (blockIndex state') `S.difference` S.fromList (hashBlock <$> blocks)
        }

appendBlock :: Block -> ChainState -> ChainState
appendBlock block state =
  state
    { preferredChain = block : preferredChain state
    , blockIndex = M.insert (hashBlock block) block $ blockIndex state
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

blocksMissingFromChain :: Chain -> ChainState -> [BlockHash]
blocksMissingFromChain = (nub .) . missingParents

missingBlocks :: ChainState -> [BlockHash]
missingBlocks state@ChainState{preferredChain} = blocksMissingFromChain preferredChain state

addChain :: Chain -> ChainState -> ChainState
addChain blocks state =
  let
    indexBlock block = M.insert (hashBlock block) block
   in
    state
      { blockIndex = foldr' indexBlock (blockIndex state) blocks
      }

addBlock :: Block -> ChainState -> ChainState
addBlock block state =
  let
    bhash = hashBlock block
   in
    if bhash `M.member` blockIndex state
      then state
      else
        state
          { blockIndex = M.insert (hashBlock block) block $ blockIndex state
          , danglingBlocks =
              (if bhash `elem` fmap hashBlock (preferredChain state) then id else S.insert bhash) $
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
              (if bhash `elem` fmap hashBlock (preferredChain state) then id else S.insert bhash) $
                danglingBlocks state
          , danglingVotes = S.insert vhash $ danglingVotes state
          , votesByRound = M.insertWith M.union r (M.singleton bhash $ S.singleton vhash) $ votesByRound state
          }

addBody :: BlockBody -> ChainState -> ChainState
addBody body state =
  let
    bhash = hashBody body
   in
    if bhash `M.member` bodyIndex state
      then state
      else state{bodyIndex = M.insert bhash body $ bodyIndex state}

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
lookupRoundForChain r state blocks =
  M.restrictKeys
    (r `lookupRound` state)
    (S.fromList $ hashBlock <$> blocks)

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

eligibleDanglingVotes :: ChainState -> [Vote]
eligibleDanglingVotes state =
  -- FIXME: This is not faithful to the March version of the Peras pseudo-code.
  let hashes = M.keysSet (blockIndex state) `S.difference` danglingBlocks state
      votes =
        filter ((== Right True) . fmap (flip S.member hashes . blockHash) . flip lookupVote' state)
          . S.toList
          $ danglingVotes state
   in M.elems . M.restrictKeys (voteIndex state) $ S.fromList votes

filterDanglingVotes :: (VoteWithBlock -> Bool) -> ChainState -> ChainState
filterDanglingVotes f state =
  state
    { danglingVotes = S.filter (either (const False) f . flip lookupVote state) $ danglingVotes state
    }

blockInWindow :: (SlotNumber, SlotNumber) -> Block -> Bool
blockInWindow (oldest, newest) MkBlock{slotNumber} = oldest <= slotNumber && slotNumber <= newest

blocksInWindow :: (SlotNumber, SlotNumber) -> Chain -> [Block]
blocksInWindow window = filter (blockInWindow window)

buildChain :: Block -> ChainState -> Either [BlockHash] Chain
buildChain block ChainState{blockIndex} =
  let
    buildChain' block'@MkBlock{parentBlock} (blocksFound, blocksMissing)
      | parentBlock == genesisHash = (blocksFound', blocksMissing)
      | otherwise = case parentBlock `M.lookup` blockIndex of
          Just block'' -> buildChain' block'' (blocksFound', blocksMissing)
          Nothing -> (blocksFound', pure parentBlock)
     where
      blocksFound' = block' : blocksFound
   in
    case buildChain' block mempty of
      (blocksFound, []) -> Right $ reverse blocksFound
      (_, blocksMissing) -> Left blocksMissing
