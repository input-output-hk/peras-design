{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}

module Peras.NodeModelSpec where

import Data.Functor (void)
import Peras.Node.IOSim (runPropInIOSim)
import Peras.Node.Netsim (runPropInNetSim)
import Peras.NodeModel (Action (..), NodeModel (..))
import Test.Hspec (Spec, describe)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Property, property, within)
import Test.QuickCheck.DynamicLogic (DL, action, anyActions_, forAllDL, getModelStateDL)
import Test.QuickCheck.Monadic (assert)
import Test.QuickCheck.StateModel (Actions, runActions)

spec :: Spec
spec = do
  describe "IOSim Honest node" $
    prop "mints blocks according to stakes" (propHonestNodeMintingRate propNodeModelIOSim)
  describe "Netsim Honest node" $
    prop "mints blocks according to stakes" (propHonestNodeMintingRate propNodeModelNetSim)

propHonestNodeMintingRate ::
  (Actions NodeModel -> Property) ->
  Property
propHonestNodeMintingRate runProp =
  within 50000000 $
    forAllDL chainProgress runProp

chainProgress :: DL NodeModel ()
chainProgress = do
  anyActions_
  getModelStateDL >>= \NodeModel{forgedBlocks} ->
    void $ action (ForgedBlocksRespectSchedule forgedBlocks)

propNodeModelIOSim ::
  Actions NodeModel ->
  Property
propNodeModelIOSim actions =
  property $
    runPropInIOSim $ do
      _ <- runActions actions
      assert True

propNodeModelNetSim :: Actions NodeModel -> Property
propNodeModelNetSim actions =
  property $
    runPropInNetSim $ do
      _ <- runActions actions
      assert True
