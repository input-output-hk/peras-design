module Peras.OptimalModelSpec (
  spec,
  propSimulate,
  simulate,
  propOptimalModelExample,
  runPropExampleNode,
) where

import Control.Monad.State (evalStateT)
import Data.Default (def)
import Data.Functor (void)
import Peras.OptimalModel (ExampleNode, NodeModel, RunMonad (runMonad), initialize)
import Test.Hspec (Spec, describe)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Gen, Property, Testable, expectFailure, property)
import Test.QuickCheck.DynamicLogic (DL, action, anyActions_, forAllDL)
import Test.QuickCheck.Gen.Unsafe (Capture (..), capture)
import Test.QuickCheck.Monadic (PropertyM, assert, monadic')
import Test.QuickCheck.StateModel (Actions, runActions)

spec :: Spec
spec =
  describe "Example node"
    . prop "Simulation respects model"
    . expectFailure -- FIXME: Remove this after the buggy example node is made honest.
    $ propSimulate propOptimalModelExample

-- | Test whether the simulation conforms to the model.
propSimulate :: (Actions NodeModel -> Property) -> Property
propSimulate = forAllDL simulate

-- | Initialize and simulate the node.
simulate :: DL NodeModel ()
simulate = action initialize >> anyActions_

-- | Act on the example node.
propOptimalModelExample :: Actions NodeModel -> Property
propOptimalModelExample actions =
  property $
    runPropExampleNode $ do
      void $ runActions actions
      assert True

-- | Test a property in the example node.
runPropExampleNode :: Testable a => PropertyM (RunMonad ExampleNode Gen) a -> Gen Property
runPropExampleNode p = do
  Capture eval <- capture
  -- FIXME: How can we evaluate this in a monad other than `Gen`?
  flip evalStateT def . runMonad . eval $ monadic' p

--------------------------------------------------------------------------------

-- Notes

{-

optimal : ∀ (c : Chain) (t : tT) (sl : Slot)
  → let b = bestChain sl t
    in
    ValidChain {block₀} {IsSlotLeader} {IsBlockSignature} c
  → c ⊆ allBlocksUpTo sl t
  → ∥ c , certs t c ∥ ≤ ∥ b , certs t b ∥

-}
