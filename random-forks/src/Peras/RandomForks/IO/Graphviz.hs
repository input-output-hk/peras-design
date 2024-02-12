{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.RandomForks.IO.Graphviz (
  chainGraph,
  peersGraph,
  writeGraph,
) where

import Data.List (intercalate, nub)
import Peras.RandomForks.Chain (blocks)
import Peras.RandomForks.Types (Block (..), Chain, PeerName (getPeerName), PeerState (..), Peers (..), Vote (..))

import qualified Data.ByteString.Base16 as B16
import qualified Data.ByteString.Char8 as BS8
import qualified Data.ByteString.Short as SBS
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
  Peers ->
  G.Graph
peersGraph Peers{getPeers = peers} =
  let nodeIds = M.mapWithKey (\name _ -> G.NodeId (G.StringId $ getPeerName name) Nothing) peers
      mkNode name PeerState{currency, vrfOutput, slotLeader, committeeMember} =
        G.NodeStatement
          (nodeIds M.! name)
          [ G.AttributeSetValue (G.NameId "shape") (G.StringId "record")
          , G.AttributeSetValue (G.NameId "label") . G.XmlId . G.XmlText $
              "<b>"
                <> getPeerName name
                <> "</b>"
                <> "|currency="
                <> show currency
                <> "|vrfOutput="
                <> take 6 (show vrfOutput)
                <> "|slotLeader="
                <> show slotLeader
                <> "|committeeMember="
                <> show committeeMember
          ]
      mkEdge name name' = G.EdgeStatement [G.ENodeId G.NoEdge $ nodeIds M.! name, G.ENodeId G.DirectedEdge $ nodeIds M.! name'] mempty
      mkEdges name PeerState{downstream} = mkEdge name <$> S.toList downstream
      nodes = uncurry mkNode <$> M.toList peers
      edges = concatMap (uncurry mkEdges) $ M.toList peers
   in G.Graph G.StrictGraph G.DirectedGraph (pure $ G.StringId "Peers") $
        [G.AssignmentStatement (G.NameId "rankdir") (G.StringId "LR")] <> nodes <> edges

chainGraph ::
  [Chain] ->
  G.Graph
chainGraph chains =
  let genesisId = G.NodeId (G.StringId "genesis") Nothing
      genesis =
        G.NodeStatement
          genesisId
          [ G.AttributeSetValue (G.NameId "shape") (G.StringId "oval")
          , G.AttributeSetValue (G.NameId "label") (G.StringId "genesis")
          ]
      nodeId bid = G.NodeId (G.StringId . BS8.unpack . B16.encode $ SBS.fromShort bid) Nothing
      mkNode Block{..} =
        G.NodeStatement
          (nodeId blockId)
          [ G.AttributeSetValue (G.NameId "shape") (G.StringId "record")
          , G.AttributeSetValue (G.NameId "label") . G.XmlId . G.XmlText $
              "<b>"
                <> BS8.unpack (B16.encode $ SBS.fromShort blockId)
                <> "</b>"
                <> "|slot="
                <> show slot
                <> "|creator="
                <> getPeerName creator
                <> "|votes="
                <> intercalate "," (map (\Vote{..} -> getPeerName voter <> "@" <> show votingRound) $ S.toList votes)
          ]
      nodes = mkNode <$> nub (concatMap blocks chains)
      mkEdge bid bid' = G.EdgeStatement [G.ENodeId G.NoEdge $ nodeId bid, G.ENodeId G.DirectedEdge $ nodeId bid'] mempty
      mkEdges [] = []
      mkEdges bs = zipWith mkEdge (init bs) (tail bs)
      edges = nub $ concatMap (mkEdges . fmap blockId . blocks) chains
      mkEdge' bid' = G.EdgeStatement [G.ENodeId G.NoEdge $ nodeId bid', G.ENodeId G.DirectedEdge genesisId] mempty
      edges' = nub $ mkEdge' . blockId . last <$> filter (not . null) (blocks <$> chains)
   in G.Graph G.StrictGraph G.DirectedGraph (pure $ G.StringId "Chains") $
        [G.AssignmentStatement (G.NameId "rankdir") (G.StringId "RL")] <> pure genesis <> nodes <> edges <> edges'
