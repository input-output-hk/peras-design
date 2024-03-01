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
import Test.Hspec.QuickCheck (modifyMaxSuccess, prop)
import Test.QuickCheck (Property, mapSize, property, within)
import Test.QuickCheck.DynamicLogic (DL, action, anyActions_, forAllDL, getModelStateDL)
import Test.QuickCheck.Monadic (assert)
import Test.QuickCheck.StateModel (Actions, runActions)

spec :: Spec
spec = do
  modifyMaxSuccess (const 30) $
    describe "IOSim Honest node" $
      prop "mints blocks according to stakes" (propHonestNodeMintingRate propNodeModelIOSim)
  -- NOTE: As those tests are run against a Rust node, across a FFI "barrier", they
  -- are actually quite slow hence we limit the number of required successes and
  -- reduce the size of generated test cases
  modifyMaxSuccess (const 20) $
    describe "Netsim Honest node" $
      prop
        "mints blocks according to stakes"
        (mapSize (`div` 10) $ propHonestNodeMintingRate propNodeModelNetSim)

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
