module Peras.ConformanceSpec (
  propBuggyNode,
  propPerfectNode,
  propSimulate,
  runPropBuggyNode,
  runPropPerfectNode,
  simulate,
  spec,
) where

import Control.Monad.State (evalStateT)
import Data.Default (def)
import Data.Functor (void)
import Peras.QCD.Node.Conformance (RunMonad (runMonad))
import Peras.QCD.Node.Impl.Buggy (BuggyNode)
import Peras.QCD.Node.Impl.Perfect (PerfectNode)
import Peras.QCD.Node.Model (NodeModel)
import Test.Hspec (Spec, describe)
import Test.Hspec.QuickCheck (modifyMaxSuccess, prop)
import Test.QuickCheck (Gen, Property, Testable, expectFailure, property)
import Test.QuickCheck.DynamicLogic (DL, anyActions_, forAllDL)
import Test.QuickCheck.Gen.Unsafe (Capture (..), capture)
import Test.QuickCheck.Monadic (PropertyM, assert, monadic')
import Test.QuickCheck.StateModel (Actions, runActions)

-- | Test against the Agda executable specification.
spec :: Spec
spec =
  modifyMaxSuccess (const 50) $
    do
      describe "Perfect node"
        . prop "Simulation respects model"
        $ propSimulate propPerfectNode
      describe "Buggy node"
        . prop "Simulation respects model"
        . expectFailure
        $ propSimulate propBuggyNode

-- | Test whether the simulation conforms to the model.
propSimulate :: (Actions NodeModel -> Property) -> Property
propSimulate = forAllDL simulate

-- | Initialize and simulate the node.
simulate :: DL NodeModel ()
simulate = anyActions_

-- | Act on the perfect node.
propPerfectNode :: Actions NodeModel -> Property
propPerfectNode actions =
  property $
    runPropPerfectNode $ do
      void $ runActions actions
      assert True

-- | Test a property in the perfect node.
runPropPerfectNode :: Testable a => PropertyM (RunMonad PerfectNode Gen) a -> Gen Property
runPropPerfectNode p = do
  Capture eval <- capture
  -- FIXME: How can we evaluate this in a monad other than `Gen`?
  flip evalStateT def . runMonad . eval $ monadic' p

-- | Act on the buggy node.
propBuggyNode :: Actions NodeModel -> Property
propBuggyNode actions =
  property $
    runPropBuggyNode $ do
      void $ runActions actions
      assert True

-- | Test a property in the buggy node.
runPropBuggyNode :: Testable a => PropertyM (RunMonad BuggyNode Gen) a -> Gen Property
runPropBuggyNode p = do
  Capture eval <- capture
  -- FIXME: How can we evaluate this in a monad other than `Gen`?
  flip evalStateT def . runMonad . eval $ monadic' p
