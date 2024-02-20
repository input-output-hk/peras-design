{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.GraphViz (
  chainGraph,
  peersGraph,
  writeGraph,
) where

import Control.Lens ((^.))
import Data.Function (on)
import Data.List (intercalate, nub, sortBy)
import Peras.Block (Block (..))
import Peras.Chain (Chain (..))
import Peras.IOSim.Network.Types (NetworkState, chainsSeen, currentStates)
import Peras.IOSim.Node.Types (committeeMember, downstreams, slotLeader, stake, vrfOutput)
import Peras.IOSim.Types (Vote (..))

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Language.Dot.Pretty as G
import qualified Language.Dot.Syntax as G

show' :: Show a => a -> String
show' = init . tail . show

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
      nodeIds = M.mapWithKey (\name _ -> G.NodeId (G.StringId $ show name) Nothing) nodeStates
      mkNode name nodeState =
        G.NodeStatement
          (nodeIds M.! name)
          [ G.AttributeSetValue (G.NameId "shape") (G.StringId "record")
          , G.AttributeSetValue (G.NameId "label") . G.XmlId . G.XmlText $
              "<b>"
                <> show' name
                <> "</b>"
                <> "|Stake "
                <> show (nodeState ^. stake)
                <> "|VrfOutput "
                <> take 6 (show $ nodeState ^. vrfOutput)
                <> "|SlotLeader "
                <> show (nodeState ^. slotLeader)
                <> "|CommitteeMember "
                <> show (nodeState ^. committeeMember)
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
  let chains = S.toList (networkState ^. chainsSeen)
      genesisId = G.NodeId (G.StringId "genesis") Nothing
      genesis =
        G.NodeStatement
          genesisId
          [ G.AttributeSetValue (G.NameId "shape") (G.StringId "oval")
          , G.AttributeSetValue (G.NameId "label") (G.StringId "genesis")
          ]
      nodeId bid = G.NodeId (G.StringId $ show' bid) Nothing
      sortVotes = compare `on` (\Vote{..} -> (votingRound, voter, voteForBlock))
      showVotes [] = ""
      showVotes vs = "|" <> intercalate "|" (showVote <$> sortBy sortVotes vs)
      showVote Vote{votingRound, voter, voteForBlock = Block{signature}} =
        "Round " <> show votingRound <> ": " <> show' voter <> " voted for " <> show' signature
      -- FIXME: The Agda types don't handle block hashes yet, so we use the signature as a placehodler for now.
      mkNode Block{..} =
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
                <> show' creatorId
                <> showVotes (S.toList includedVotes)
          ]
      blocks Genesis = []
      blocks (Cons b p) = b : blocks p
      nodes = mkNode <$> nub (concatMap blocks chains)
      mkEdge bid bid' = G.EdgeStatement [G.ENodeId G.NoEdge $ nodeId bid, G.ENodeId G.DirectedEdge $ nodeId bid'] mempty
      mkEdges [] = []
      mkEdges bs = zipWith mkEdge (init bs) (tail bs)
      edges = nub $ concatMap (mkEdges . fmap signature . blocks) chains
      mkEdge' bid' = G.EdgeStatement [G.ENodeId G.NoEdge $ nodeId bid', G.ENodeId G.DirectedEdge genesisId] mempty
      edges' = nub $ mkEdge' . signature . last <$> filter (not . null) (blocks <$> chains)
   in G.Graph G.StrictGraph G.DirectedGraph (pure $ G.StringId "Chains") $
        [G.AssignmentStatement (G.NameId "rankdir") (G.StringId "RL")] <> pure genesis <> nodes <> edges <> edges'
