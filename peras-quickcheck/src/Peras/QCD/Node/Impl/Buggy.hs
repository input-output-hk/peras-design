{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Peras.QCD.Node.Impl.Buggy (
  BuggyNode,
) where

import Control.Monad.State (State, runState)
import Data.Bifunctor (first, second)
import Data.Default (Default (..))
import GHC.Generics (Generic)
import Peras.QCD.Node.API (PerasNode (..))
import Peras.QCD.Types (Message)
import Test.QuickCheck (Gen, oneof)

import qualified Peras.QCD.Node.Model as Specification (NodeModel, emptyNode)
import qualified Peras.QCD.Node.Specification as Specification (blockCreation, fetching, initialize, voting)

newtype BuggyNode = BuggyNode {model :: Specification.NodeModel}
  deriving (Generic, Show)

instance Default BuggyNode where
  def = BuggyNode Specification.emptyNode

instance PerasNode BuggyNode Gen where
  initialize params party = careless $ Specification.initialize params party
  fetching chains votes = careless $ Specification.fetching chains votes
  blockCreation txs = careless $ Specification.blockCreation txs
  voting weight = careless $ Specification.voting weight

careless :: State Specification.NodeModel [Message] -> BuggyNode -> Gen ([Message], BuggyNode)
careless action state =
  oneof
    [ -- Flawless.
      pure result
    , -- Discard the message.
      pure $ first (const mempty) result
    , -- Don't result at all.
      pure (mempty, state)
    ]
 where
  result :: ([Message], BuggyNode)
  result = second BuggyNode . runState action . model $ state
