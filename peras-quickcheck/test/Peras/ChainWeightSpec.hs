{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE TypeApplications #-}

module Peras.ChainWeightSpec (
  spec,
) where

import Control.Monad.State (evalStateT)
import Data.Default (Default (..))
import Data.Functor (void)
import Peras.ChainWeight (BuggyNode, PerfectNode, RunMonad (runMonad))
import Peras.SmallStep.Experiment.Types (NodeState)
import Test.Hspec (Spec, describe)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Gen, Property, Testable, expectFailure, property)
import Test.QuickCheck.DynamicLogic (DL, anyActions_, forAllDL, getModelStateDL)
import Test.QuickCheck.Gen.Unsafe (Capture (..), capture)
import Test.QuickCheck.Monadic (PropertyM, assert, monadic')
import Test.QuickCheck.StateModel (Actions, RunModel, runActions)

import qualified Peras.SmallStep.Experiment as ES (propNeverShortens)
import qualified Test.QuickCheck.DynamicLogic as DL (assert)

-- | Test against the Agda executable specification.
spec :: Spec
spec =
  do
    describe "Perfect node" $
      do
        prop "Simulation respects model"
          . propSimulate
          $ propNode @PerfectNode def
        prop "Preferred chain never shortens"
          . propNeverShortens
          $ propNode @PerfectNode def
    describe "Buggy node" $
      do
        prop "Simulation respects model"
          . expectFailure
          . propSimulate
          $ propNode @BuggyNode def
        prop "Preferred chain never shortens"
          . expectFailure
          . propNeverShortens
          $ propNode @BuggyNode def

-- | Test whether the simulation conforms to the model.
propSimulate :: (Actions NodeState -> Property) -> Property
propSimulate = forAllDL simulate

-- | Initialize and simulate the node.
simulate :: DL NodeState ()
simulate = anyActions_

propNeverShortens :: (Actions NodeState -> Property) -> Property
propNeverShortens =
  forAllDL $
    do
      anyActions_
      initial <- getModelStateDL
      anyActions_
      final <- getModelStateDL
      DL.assert "Final weight not less than initial weight" $
        ES.propNeverShortens (initial :: NodeState) (final :: NodeState)

-- | Act on the perfect node.
propNode :: RunModel NodeState (RunMonad s Gen) => s -> Actions NodeState -> Property
propNode initial actions =
  property $
    runPropNode initial $ do
      void $ runActions actions
      assert True

-- | Test a property in the perfect node.
runPropNode :: Testable a => s -> PropertyM (RunMonad s Gen) a -> Gen Property
runPropNode initial p = do
  Capture eval <- capture
  flip evalStateT initial . runMonad . eval $ monadic' p
