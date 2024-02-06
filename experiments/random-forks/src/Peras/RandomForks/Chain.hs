{-# LANGUAGE RecordWildCards #-}

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
    
newtype Chain =
  Chain
  {
    blocks :: [Block]
  }
    deriving (Eq, Ord, Read, Show)

instance Semigroup Chain where
  Chain x <> Chain y = Chain $ x <> y

instance Monoid Chain where
  mempty = Chain mempty

chainLength
  :: Chain
  -> Int
chainLength = length . blocks

extendChain
  :: Chain
  -> Block
  -> Chain
extendChain = (. (Chain . pure)) . (<>)

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
