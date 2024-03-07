{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.GraphViz (
  chainGraph,
  peersGraph,
  writeGraph,
) where

import Control.Lens ((^.))
import Data.Function (on)
import Data.List (intercalate, sortBy)
import Peras.Block (Block (..))
import Peras.Chain (RoundNumber (roundNumber), Vote (..))
import Peras.IOSim.Hash (genesisHash)
import Peras.IOSim.Network.Types (NetworkState, blocksSeen, currentStates, votesSeen)
import Peras.IOSim.Node.Types (committeeMember, downstreams, rxBytes, slotLeader, stake, txBytes, vrfOutput)
import Peras.Message (NodeId (..))

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Language.Dot.Pretty as G
import qualified Language.Dot.Syntax as G

show' :: Show a => a -> String
show' = dropWhile (== '"') . reverse . dropWhile (== '"') . reverse . show

writeGraph ::
  FilePath ->
  G.Graph ->
  IO ()
writeGraph = (. G.renderDot) . writeFile

peersGraph ::
  NetworkState ->
  G.Graph
peersGraph networkState =
  let nodeStates = networkState ^. currentStates
      nodeIds = M.mapWithKey (\name _ -> G.NodeId (G.StringId $ nodeId name) Nothing) nodeStates
      mkNode name nodeState =
        G.NodeStatement
          (nodeIds M.! name)
          [ G.AttributeSetValue (G.NameId "shape") (G.StringId "record")
          , G.AttributeSetValue (G.NameId "label") . G.XmlId . G.XmlText $
              "<b>"
                <> nodeId name
                <> "</b>"
                <> "|Stake "
                <> show (nodeState ^. stake)
                <> "|VrfOutput "
                <> take 6 (show $ nodeState ^. vrfOutput)
                <> "|SlotLeader "
                <> show (nodeState ^. slotLeader)
                <> "|CommitteeMember "
                <> show (nodeState ^. committeeMember)
                <> "|Rx/Tx (kB)"
                <> show (nodeState ^. rxBytes `div` 1024)
                <> "/"
                <> show (nodeState ^. txBytes `div` 1024)
          ]
      mkEdge name name' = G.EdgeStatement [G.ENodeId G.NoEdge $ nodeIds M.! name, G.ENodeId G.DirectedEdge $ nodeIds M.! name'] mempty
      mkEdges name nodeState = mkEdge name <$> S.toList (nodeState ^. downstreams)
      nodes = uncurry mkNode <$> M.toList nodeStates
      edges = concatMap (uncurry mkEdges) $ M.toList nodeStates
   in G.Graph G.StrictGraph G.DirectedGraph (pure $ G.StringId "Peers") $
        [G.AssignmentStatement (G.NameId "rankdir") (G.StringId "LR")] <> nodes <> edges

chainGraph ::
  NetworkState ->
  G.Graph
chainGraph networkState =
  let tree = networkState ^. Peras.IOSim.Network.Types.blocksSeen
      allVotes = networkState ^. votesSeen
      genesisId = G.NodeId (G.StringId "genesis") Nothing
      genesis =
        G.NodeStatement
          genesisId
          [ G.AttributeSetValue (G.NameId "shape") (G.StringId "oval")
          , G.AttributeSetValue (G.NameId "label") (G.StringId "genesis")
          ]
      nodeId bid = G.NodeId (G.StringId $ show' bid) Nothing
      sortVotes = compare `on` (\MkVote{..} -> (votingRound, creatorId, blockHash))
      votesInBlock = fmap (allVotes M.!) . includedVotes
      showVotes [] = ""
      showVotes vs = "|" <> intercalate "|" (showVote <$> sortBy sortVotes vs)
      showVote MkVote{votingRound, creatorId, blockHash} =
        "Round " <> show (roundNumber votingRound) <> ": " <> show creatorId <> " voted for " <> show' blockHash
      mkNode block@Block{..} =
        G.NodeStatement
          (nodeId signature)
          [ G.AttributeSetValue (G.NameId "shape") (G.StringId "record")
          , G.AttributeSetValue (G.NameId "label") . G.XmlId . G.XmlText $
              "<b>"
                <> show' signature
                <> "</b>"
                <> "|Slot "
                <> show slotNumber
                <> "|Creator "
                <> show creatorId
                <> showVotes (votesInBlock block)
          ]
      blocks = S.toList . S.unions $ M.elems tree
      nodes = mkNode <$> blocks
      mkEdge bid bid' = G.EdgeStatement [G.ENodeId G.NoEdge bid', G.ENodeId G.DirectedEdge bid] mempty
      mkEdges bid bs
        | bid == genesisHash = mkEdge genesisId . nodeId . Peras.Block.signature <$> S.toList bs
        | otherwise = mkEdge (nodeId bid) . nodeId . Peras.Block.signature <$> S.toList bs
      edges = M.foldMapWithKey mkEdges tree
   in G.Graph G.StrictGraph G.DirectedGraph (pure $ G.StringId "Chains") $
        [G.AssignmentStatement (G.NameId "rankdir") (G.StringId "RL")] <> pure genesis <> nodes <> edges
