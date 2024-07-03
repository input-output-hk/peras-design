{-# LANGUAGE NamedFieldPuns #-}

module Peras.Prototype.Visualizer where

import Control.Tracer
import Data.Foldable (toList)
import Data.IORef
import qualified Data.Set as Set
import qualified Language.Dot.Pretty as G
import qualified Language.Dot.Syntax as G
import Peras.Block as Block (Block (..), Certificate (..))
import Peras.Chain as Vote (Vote (..))
import Peras.Numbering
import Peras.Prototype.Trace (PerasLog (CastVote, NewChainAndVotes))
import Prelude hiding (round)

type VisTracer = Tracer IO PerasLog

type VisReader = IO [PerasLog]

makeVisTracer :: IO (VisTracer, VisReader)
makeVisTracer =
  do
    ref <- newIORef mempty
    pure
      ( Tracer . emit $ modifyIORef ref . (:)
      , reverse <$> readIORef ref
      )

writeGraph :: FilePath -> G.Graph -> IO ()
writeGraph = (. G.renderDot) . writeFile

visualize :: [PerasLog] -> G.Graph
visualize events =
  let
    extractBlocks (NewChainAndVotes _ cs _) = concat cs
    extractBlocks _ = mempty
    allBlocks = toList . Set.fromList $ concatMap extractBlocks events
    mkNodeEdge MkBlock{Block.creatorId, slotNumber, Block.signature, certificate} =
      G.NodeStatement
        (flip G.NodeId Nothing . G.StringId . ("block" <>) $ show' signature)
        [ G.AttributeSetValue (G.NameId "shape") (G.StringId "record")
        , G.AttributeSetValue (G.NameId "label") . G.XmlId . G.XmlText $
            "<b>"
              <> take 8 (show' signature)
              <> "</b>"
              <> "|Slot "
              <> show (getSlotNumber slotNumber)
              <> "|Creator "
              <> show creatorId
              <> maybe "" (("|<i>Certificate " <>) . (<> "</i>") . show . getRoundNumber . round) certificate
        ]
    mkBlockEdge MkBlock{Block.signature, parentBlock} =
      G.EdgeStatement
        [ G.ENodeId G.NoEdge . flip G.NodeId Nothing . G.StringId . ("block" <>) $ show' signature
        , G.ENodeId G.DirectedEdge . flip G.NodeId Nothing . G.StringId . ("block" <>) $ show' parentBlock
        ]
        mempty
    genesis =
      G.NodeStatement
        (flip G.NodeId Nothing $ G.StringId "block")
        [ G.AttributeSetValue (G.NameId "shape") (G.StringId "oval")
        , G.AttributeSetValue (G.NameId "label") (G.StringId "genesis")
        ]
    blockNodes = mkNodeEdge <$> allBlocks
    blockEdges = mkBlockEdge <$> allBlocks
    extractVotes (CastVote _ v) = pure v
    extractVotes _ = mempty
    allVotes = toList . Set.fromList $ concatMap extractVotes events
    mkVoteNode MkVote{Vote.creatorId, votingRound, Vote.signature} =
      G.NodeStatement
        (flip G.NodeId Nothing . G.StringId . ("vote" <>) $ show' signature)
        [ G.AttributeSetValue (G.NameId "shape") (G.StringId "oval")
        , G.AttributeSetValue (G.NameId "label") . G.StringId $
            "Voter "
              <> show creatorId
              <> "\\nRound "
              <> show (getRoundNumber votingRound)
        ]
    mkVoteEdge MkVote{blockHash, Vote.signature} =
      G.EdgeStatement
        [ G.ENodeId G.NoEdge . flip G.NodeId Nothing . G.StringId . ("vote" <>) $ show' signature
        , G.ENodeId G.DirectedEdge . flip G.NodeId Nothing . G.StringId . ("block" <>) $ show' blockHash
        ]
        [ G.AttributeSetValue (G.NameId "style") (G.StringId "dashed")
        ]
    voteNodes = mkVoteNode <$> allVotes
    voteEdges = mkVoteEdge <$> allVotes
   in
    G.Graph G.StrictGraph G.DirectedGraph (pure $ G.StringId "Chains") $
      [G.AssignmentStatement (G.NameId "rankdir") (G.StringId "RL")]
        <> pure genesis
        <> blockNodes
        <> blockEdges
        <> voteNodes
        <> voteEdges

show' :: Show a => a -> String
show' = init . tail . show
