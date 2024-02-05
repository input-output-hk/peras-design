{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

module Peras.RandomForks.Peer (
  Peers (..),
  PeerName (..),
  PeerState (..),
  randomPeers,
  peerGraph,
) where

import Data.List (delete)
import Data.Maybe (fromMaybe)
import Peras.RandomForks.Protocol (Parameters (..), Protocol (..), isCommitteMember, isSlotLeader)
import System.Random (randomRIO)

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Language.Dot.Syntax as G

newtype Peers = Peers {getPeers :: M.Map PeerName PeerState}
  deriving (Eq, Ord, Read, Show)

newtype PeerName = PeerName {getPeerName :: String}
  deriving (Eq, Ord, Read, Show)

data PeerState = PeerState
  { currency :: Int
  , vrfOutput :: Double
  , slotLeader :: Bool
  , committeeMember :: Bool
  , upstream :: S.Set PeerName
  , downstream :: S.Set PeerName
  }
  deriving (Eq, Ord, Read, Show)

randomPeers ::
  Parameters ->
  Protocol ->
  IO Peers
randomPeers Parameters{..} protocol =
  do
    let
      peerNames = PeerName . ("Peer " <>) . show <$> [1 .. peerCount]
      randomSubset 0 _ = pure mempty
      randomSubset n items =
        do
          item <- (items !!) <$> randomRIO (0, length items - 1)
          S.insert item <$> randomSubset (n - 1) (delete item items)
    downstreams <- M.fromList <$> mapM (\name -> (name,) <$> randomSubset downstreamCount (delete name peerNames)) peerNames
    let
      upstreams = M.fromListWith (<>) . concatMap (\(name, names) -> (,S.singleton name) <$> S.toList names) $ M.toList downstreams
      randomPeer name =
        do
          currency <- randomRIO (1, maximumCurrency)
          vrfOutput <- randomRIO (0, 1)
          slotLeader <- isSlotLeader protocol currency
          committeeMember <- isCommitteMember protocol currency
          let upstream = fromMaybe mempty $ M.lookup name upstreams
              downstream = fromMaybe mempty $ M.lookup name downstreams
          pure PeerState{..}
    Peers . M.fromList <$> mapM (\name -> (name,) <$> randomPeer name) peerNames

peerGraph ::
  Peers ->
  G.Graph
peerGraph Peers{getPeers = peers} =
  let
    nodeIds = M.mapWithKey (\name _ -> G.NodeId (G.StringId $ getPeerName name) Nothing) peers
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
   in
    G.Graph G.StrictGraph G.DirectedGraph (pure $ G.StringId "Peers") $
      [G.AssignmentStatement (G.NameId "rankdir") (G.StringId "LR")] <> nodes <> edges
