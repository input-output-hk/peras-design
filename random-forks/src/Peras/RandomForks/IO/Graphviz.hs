{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.RandomForks.IO.Graphviz (
  chainGraph
, peersGraph
, writeGraph
) where

import Data.List (nub)
import Peras.RandomForks.Chain
import Peras.RandomForks.Peer
import Peras.RandomForks.Types

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Language.Dot.Pretty as G
import qualified Language.Dot.Syntax as G

writeGraph
  :: FilePath
  -> G.Graph
  -> IO ()
writeGraph = (. G.renderDot) . writeFile

peersGraph
  :: Peers
  -> G.Graph
peersGraph Peers{getPeers = peers} =
  let
    nodeIds = M.mapWithKey (\name _ -> G.NodeId (G.StringId $ getPeerName name) Nothing) peers
    mkNode name PeerState{currency,vrfOutput,slotLeader,committeeMember} =
      G.NodeStatement (nodeIds M.! name)
        [
          G.AttributeSetValue (G.NameId "shape") (G.StringId "record")
        , G.AttributeSetValue (G.NameId "label") . G.XmlId . G.XmlText
           $ "<b>" <> getPeerName name <> "</b>"
           <> "|currency=" <> show currency
           <> "|vrfOutput=" <> take 6 (show vrfOutput)
           <> "|slotLeader=" <> show slotLeader
           <> "|committeeMember=" <> show committeeMember
        ]
    mkEdge name name' = G.EdgeStatement [G.ENodeId G.NoEdge $ nodeIds M.! name, G.ENodeId G.DirectedEdge $ nodeIds M.! name'] mempty
    mkEdges name PeerState{downstream} = mkEdge name <$> S.toList downstream
    nodes = uncurry mkNode <$> M.toList peers
    edges = concatMap (uncurry mkEdges) $ M.toList peers
  in
    G.Graph G.StrictGraph G.DirectedGraph (pure $ G.StringId "Peers")
      $ [G.AssignmentStatement (G.NameId "rankdir") (G.StringId "LR")] <> nodes <> edges


chainGraph
  :: [Chain]
  -> G.Graph
chainGraph chains =
  let
    genesisId = G.NodeId (G.StringId "genesis") Nothing
    genesis =
      G.NodeStatement genesisId
        [
          G.AttributeSetValue (G.NameId "shape") (G.StringId "oval")
        , G.AttributeSetValue (G.NameId "label") (G.StringId "genesis")
        ]
    nodeId bid = G.NodeId (G.StringId $ show bid) Nothing
    mkNode Block{..} =
      G.NodeStatement (nodeId blockId)
        [
          G.AttributeSetValue (G.NameId "shape") (G.StringId "record")
        , G.AttributeSetValue (G.NameId "label") . G.XmlId . G.XmlText
            $ "<b>" <> take 8 (show blockId) <> "</b>"
            <> "|slot=" <> show slot
            <> "|creator=" <> getPeerName creator
        ]
    nodes = mkNode <$> nub (concatMap blocks chains)
    mkEdge bid bid' = G.EdgeStatement [G.ENodeId G.NoEdge $ nodeId bid, G.ENodeId G.DirectedEdge $ nodeId bid'] mempty
    mkEdges [] = []
    mkEdges bs = zipWith mkEdge (init bs) (tail bs)
    edges = nub $ concatMap (mkEdges . fmap blockId . blocks) chains
    mkEdge' bid' = G.EdgeStatement [G.ENodeId G.NoEdge genesisId, G.ENodeId G.DirectedEdge $ nodeId bid'] mempty
    edges' = nub $ mkEdge' . blockId . head <$> filter (not . null) (blocks <$> chains)
  in
    G.Graph G.StrictGraph G.DirectedGraph (pure $ G.StringId "Chains")
      $ [G.AssignmentStatement (G.NameId "rankdir") (G.StringId "LR")] <> pure genesis <> nodes <> edges <> edges'
