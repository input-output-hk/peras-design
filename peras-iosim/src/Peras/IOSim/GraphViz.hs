{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.GraphViz (
  chainGraph,
  peersGraph,
  writeGraph,
) where

import Control.Lens ((^.))
import Data.List (nub)
import Peras.Block (Block (..))
import Peras.Chain (Chain (..))
import Peras.IOSim.Network.Types (NetworkState, exitStates)
import Peras.IOSim.Node.Types (committeeMember, downstreams, preferredChain, slotLeader, stake, vrfOutput)

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Language.Dot.Pretty as G
import qualified Language.Dot.Syntax as G

writeGraph ::
  FilePath ->
  G.Graph ->
  IO ()
writeGraph = (. G.renderDot) . writeFile

peersGraph ::
  NetworkState v ->
  G.Graph
peersGraph networkState =
  let nodeStates = networkState ^. exitStates
      nodeIds = M.mapWithKey (\name _ -> G.NodeId (G.StringId $ show name) Nothing) nodeStates
      mkNode name nodeState =
        G.NodeStatement
          (nodeIds M.! name)
          [ G.AttributeSetValue (G.NameId "shape") (G.StringId "record")
          , G.AttributeSetValue (G.NameId "label") . G.XmlId . G.XmlText $
              "<b>"
                <> show name
                <> "</b>"
                <> "|stake="
                <> show (nodeState ^. stake)
                <> "|vrfOutput="
                <> take 6 (show $ nodeState ^. vrfOutput)
                <> "|slotLeader="
                <> show (nodeState ^. slotLeader)
                <> "|committeeMember="
                <> show (nodeState ^. committeeMember)
          ]
      mkEdge name name' = G.EdgeStatement [G.ENodeId G.NoEdge $ nodeIds M.! name, G.ENodeId G.DirectedEdge $ nodeIds M.! name'] mempty
      mkEdges name nodeState = mkEdge name <$> S.toList (nodeState ^. downstreams)
      nodes = uncurry mkNode <$> M.toList nodeStates
      edges = concatMap (uncurry mkEdges) $ M.toList nodeStates
   in G.Graph G.StrictGraph G.DirectedGraph (pure $ G.StringId "Peers") $
        [G.AssignmentStatement (G.NameId "rankdir") (G.StringId "LR")] <> nodes <> edges

chainGraph ::
  Eq v =>
  Show v =>
  NetworkState v ->
  G.Graph
chainGraph networkState =
  let chains = (^. preferredChain) <$> M.elems (networkState ^. exitStates)
      genesisId = G.NodeId (G.StringId "genesis") Nothing
      genesis =
        G.NodeStatement
          genesisId
          [ G.AttributeSetValue (G.NameId "shape") (G.StringId "oval")
          , G.AttributeSetValue (G.NameId "label") (G.StringId "genesis")
          ]
      nodeId bid = G.NodeId (G.StringId $ show bid) Nothing
      -- FIXME: The Agda types don't handle block hashes yet, so we use the signature as a placehodler for now.
      mkNode Block{..} =
        G.NodeStatement
          (nodeId signature)
          [ G.AttributeSetValue (G.NameId "shape") (G.StringId "record")
          , G.AttributeSetValue (G.NameId "label") . G.XmlId . G.XmlText $
              "<b>"
                <> show signature
                <> "</b>"
                <> "|slot="
                <> show slotNumber
                <> "|creator="
                <> show creatorId
                <> "|votes="
                <> show includedVotes
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
