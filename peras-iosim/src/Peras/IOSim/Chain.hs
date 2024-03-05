{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Chain (
  ChainState (..),
  BlockTree (..),
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
  IncompleteIndex (..),
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
  isBlockOnChain,
  isVoteRecordedOnChain,
  eligibleDanglingVotes,
  appendBlock,
  addBlock,
  addVote,
) where

import Control.Exception (Exception (..))
import Control.Monad (filterM, unless, (<=<))
import Control.Monad.Except (throwError)
import Data.Aeson (FromJSON, ToJSON)
import Data.Default (Default (def))
import Data.Foldable (foldr')
import Data.Maybe (fromMaybe)
import GHC.Generics (Generic)
import Peras.Block (Block (..), Slot)
import Peras.Chain (Chain (..), RoundNumber, Vote (..))
import Peras.IOSim.Hash (BlockHash, VoteHash, hashBlock, hashVote)
import Peras.IOSim.Types (Vote')
import Peras.Orphans ()
import Test.QuickCheck (Arbitrary (..))

import qualified Data.Map as M
import qualified Data.Set as S

data BlockTree
  = Genesis
  | BlockTree
      { parentBlock :: Block
      , childBlocks :: BlockTree
      }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON BlockTree
instance ToJSON BlockTree

instance Default BlockTree where
  def = Genesis

data ChainState = ChainState
  { preferredChain :: Chain
  , blockIndex :: M.Map BlockHash Block
  , voteIndex :: M.Map VoteHash Vote'
  , blockTree :: BlockTree
  , danglingBlocks :: S.Set BlockHash
  , danglingVotes :: S.Set VoteHash
  , votesByRound :: M.Map RoundNumber (M.Map BlockHash (S.Set VoteHash))
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON ChainState
instance ToJSON ChainState

instance Default ChainState where
  def = ChainState def def def def def def def

instance Arbitrary ChainState where
  arbitrary = pure def

newtype IncompleteIndex = IncompleteIndex {message :: String}
  deriving stock (Eq, Generic, Ord, Read, Show)

instance Exception IncompleteIndex where
  displayException = message

instance FromJSON IncompleteIndex
instance ToJSON IncompleteIndex

indexChain :: Chain -> Either IncompleteIndex ChainState
indexChain = flip preferChain def

preferChain :: Chain -> ChainState -> Either IncompleteIndex ChainState
preferChain chain state =
  do
    state' <- addChain chain state
    pure
      state'
        { preferredChain = chain
        , danglingBlocks = M.keysSet (blockIndex state') `S.difference` S.fromList (hashBlock <$> blocks chain)
        , danglingVotes = M.keysSet (voteIndex state') `S.difference` S.fromList (concatMap includedVotes $ blocks chain)
        }

appendBlock :: Block -> ChainState -> Either IncompleteIndex ChainState
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

addChain :: Chain -> ChainState -> Either IncompleteIndex ChainState
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
    unless blockReferencesOkay
      . throwError
      $ IncompleteIndex "Incomplete index: votes reference non-existent blocks."
    unless voteReferencesOkay
      . throwError
      $ IncompleteIndex "Incomplete index: blocks reference non-existent votes."
    pure state'

addBlock :: Block -> ChainState -> Either IncompleteIndex ChainState
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

addVote :: Vote Block -> ChainState -> Either IncompleteIndex ChainState
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

lookupBlock :: BlockHash -> ChainState -> Either IncompleteIndex Block
lookupBlock hash ChainState{blockIndex} =
  maybe (Left . IncompleteIndex $ "Incomplete index: block hash " <> show hash <> " missing from block index.") Right $
    hash `M.lookup` blockIndex

lookupVote :: VoteHash -> ChainState -> Either IncompleteIndex (Vote Block)
lookupVote hash state = resolveBlock state =<< hash `lookupVote'` state

lookupVote' :: VoteHash -> ChainState -> Either IncompleteIndex Vote'
lookupVote' hash ChainState{voteIndex} =
  maybe (Left . IncompleteIndex $ "Incomplete index: vote hash " <> show hash <> " missing from vote index.") Right $
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

resolveBlock :: ChainState -> Vote' -> Either IncompleteIndex (Vote Block)
resolveBlock state vote =
  do
    block <- blockHash vote `lookupBlock` state
    pure vote{blockHash = block}

resolveBlocksOnChain :: ChainState -> Either IncompleteIndex [Vote Block]
resolveBlocksOnChain state =
  mapM (resolveBlock state) . M.elems $
    M.withoutKeys (voteIndex state) (danglingVotes state)

votesRecordedOnChain :: Chain -> Either IncompleteIndex [Vote Block]
votesRecordedOnChain = resolveBlocksOnChain <=< indexChain

votesRecordedOnChain' :: Chain -> Either IncompleteIndex [Vote']
votesRecordedOnChain' chain =
  do
    state <- indexChain chain
    pure . M.elems $
      M.withoutKeys (voteIndex state) (danglingVotes state)

votesForBlocksOnChain :: Chain -> Either IncompleteIndex [Vote Block]
votesForBlocksOnChain chain =
  do
    state <- indexChain chain
    let hashes = M.keysSet (blockIndex state) `S.difference` danglingBlocks state
    mapM (resolveBlock state) . M.elems $
      M.filter ((`S.member` hashes) . blockHash) (voteIndex state)

votesForBlocksOnChain' :: Chain -> Either IncompleteIndex [Vote']
votesForBlocksOnChain' chain =
  do
    state <- indexChain chain
    let hashes = M.keysSet (blockIndex state) `S.difference` danglingBlocks state
    pure . M.elems $
      M.filter ((`S.member` hashes) . blockHash) (voteIndex state)

eligibleDanglingVotes :: ChainState -> Either IncompleteIndex [VoteHash]
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
