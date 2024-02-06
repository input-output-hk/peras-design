{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}

module Peras.RandomForks.Chain (
  Block(..)
, Chain(..)
, Message(..)
, chainGraph
, chainLength
, extendChain
, mkBlock
) where

import Data.List (nub)
import Data.UUID.V4 (nextRandom)
import Peras.RandomForks.Types (BlockId, PeerName(getPeerName), Slot)

import qualified Language.Dot.Syntax as G

data Block =
  Block
  {
    creator :: PeerName
  , slot :: Slot
  , blockId :: BlockId
  }
    deriving (Eq, Ord, Read, Show)

mkBlock
  :: PeerName
  -> Slot
  -> IO Block
mkBlock name slot = Block name slot <$> nextRandom

data Chain =
  Chain
  {
    block :: Block,
    prev :: Chain
  }
  | Genesis
  deriving stock (Eq, Ord, Read, Show)

blocks :: Chain -> [Block]
blocks = \case
  Genesis -> []
  Chain {block, prev} -> block : blocks prev

chainLength
  :: Chain
  -> Int
chainLength = \case
  Genesis -> 0
  Chain{prev} -> 1 + chainLength prev

extendChain
  :: Block
  -> Chain
  -> Chain
extendChain block = Chain block

data Message =
  Message
  {
    messageSlot :: Slot
  , messageChain :: Chain
  , messageDestination :: PeerName
  }
    deriving (Eq, Ord, Read, Show)


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
