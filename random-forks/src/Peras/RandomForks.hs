{-# LANGUAGE NamedFieldPuns #-}

module Peras.RandomForks (
  run
, advance
) where

import Data.Bifunctor (bimap)
import Data.Foldable (foldlM)
import Peras.RandomForks.Chain (Message(Message, messageDestination))
import Peras.RandomForks.IO.Graphviz (chainGraph, writeGraph)
import Peras.RandomForks.Peer (PeerState(pendingMessages, preferredChain), Peers(..), nextSlot)
import Peras.RandomForks.Protocol (Protocol)
import Peras.RandomForks.Types (Slot) 
import System.FilePath ((<.>))

import qualified Data.Map.Strict as M

run
  :: Protocol
  -> Maybe FilePath
  -> Peers
  -> Int
  -> IO Peers
run protocol baseName peers duration =
  foldlM (advance protocol baseName) peers [0..duration]
  
advance
  :: Protocol
  -> Maybe FilePath
  -> Peers
  -> Slot
  -> IO Peers
advance protocol baseName (Peers peers) slot =
  do
    -- Advance one slot.
    (peers', messages) <-
      bimap M.fromList mconcat . unzip
        <$> sequence
        [
          do
            (state', messages) <- nextSlot protocol slot name state
            pure ((name, state'), messages)
        |
          (name, state) <- M.toList peers  -- FIXME: Rewrite as map.
        ]
    -- Deliver any new messages.
    let
      deliverMessage ps message@Message{messageDestination} =
        M.adjust (\state -> state {pendingMessages = pendingMessages state <> pure message}) messageDestination ps
      peers'' = foldl deliverMessage peers' messages
    maybe (pure ()) (flip writeGraph (chainGraph $ preferredChain <$> M.elems peers'') . (<.> "dot") . (<> show slot)) baseName
    pure $ Peers peers''
