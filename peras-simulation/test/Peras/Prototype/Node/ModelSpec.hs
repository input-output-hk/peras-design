module Peras.Prototype.Node.ModelSpec where

import Control.Monad.State (evalStateT)
import Data.Default (def)
import Data.Functor (void)
import Peras.Prototype.Node.Model (NodeModel, RunMonad (runMonad))
import Test.Hspec (Spec, describe)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Gen, Property, Testable, property)
import Test.QuickCheck.DynamicLogic (DL, anyActions_, forAllDL)
import Test.QuickCheck.Gen.Unsafe (Capture (..), capture)
import Test.QuickCheck.Monadic (PropertyM, assert, monadic')
import Test.QuickCheck.StateModel (Actions, runActions)

-- | Test against the Agda executable specification.
spec :: Spec
spec =
  describe "Prototype node"
    . prop "Simulation respects model"
    $ propSimulate propPrototypeNode

-- | Test whether the simulation conforms to the model.
propSimulate :: (Actions NodeModel -> Property) -> Property
propSimulate = forAllDL simulate

-- | Initialize and simulate the node.
simulate :: DL NodeModel ()
simulate = anyActions_

-- | Act on the prototype node.
propPrototypeNode :: Actions NodeModel -> Property
propPrototypeNode actions =
  property $
    runPropPrototypeNode $ do
      void $ runActions actions
      assert True

-- | Test a property in the prototype node.
runPropPrototypeNode :: Testable a => PropertyM (RunMonad Gen) a -> Gen Property
runPropPrototypeNode p = do
  Capture eval <- capture
  -- FIXME: How can we evaluate this in a monad other than `Gen`?
  flip evalStateT def . runMonad . eval $ monadic' p
