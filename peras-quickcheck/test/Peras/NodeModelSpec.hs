{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}

module Peras.NodeModelSpec where

import Data.Functor (void)
import Peras.Node.IOSim (runPropInIOSim)
import Peras.NodeModel (Action (..), NodeModel (..))
import Test.Hspec (Spec)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Property, Testable, property, within)
import Test.QuickCheck.DynamicLogic (DL, action, anyActions_, forAllDL, getModelStateDL)
import Test.QuickCheck.Monadic (PropertyM, assert)
import Test.QuickCheck.StateModel (Actions, RunModel, runActions)

spec :: Spec
spec =
  prop "Honest node mints blocks according to stakes" propHonestNodeMintingRate

newtype WrapM m a = Wrap {unWrap :: forall prop. (RunModel NodeModel m, Testable prop) => PropertyM m a -> prop}

propHonestNodeMintingRate :: Property
propHonestNodeMintingRate =
  within 50000000 $
    forAllDL chainProgress propNodeModelIOSim

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
