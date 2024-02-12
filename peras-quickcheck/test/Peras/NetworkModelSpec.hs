{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Peras.NetworkModelSpec where

import Control.Monad (forM_)
import Peras.NetworkModel (Action (..), Network (..), nodes, runMonad)
import Peras.Util (runPropInIOSim)
import Test.Hspec (Spec)
import Test.Hspec.QuickCheck (modifyMaxShrinks, prop)
import Test.QuickCheck (Property, property, within)
import Test.QuickCheck.DynamicLogic (DL, action, anyActions_, forAllDL, getModelStateDL)
import Test.QuickCheck.Monadic (assert)
import Test.QuickCheck.StateModel (Actions, runActions)

spec :: Spec
spec =
  modifyMaxShrinks (const 0) $ prop "Chain progress" prop_chain_progress

prop_chain_progress :: Property
prop_chain_progress =
  within 5000000 $
    forAllDL chainProgress propNetworkModel

chainProgress :: DL Network ()
chainProgress = do
  anyActions_
  getModelStateDL >>= \Network{nodeIds} ->
    forM_ nodeIds (action . ObserveBestChain)

propNetworkModel :: Actions Network -> Property
propNetworkModel actions =
  property $
    runPropInIOSim $ do
      _ <- runActions actions
      assert True
