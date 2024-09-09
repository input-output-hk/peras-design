module Peras.Conformance.TestSpec where

import Control.Monad.State (evalStateT)
import Data.Default (def)
import Data.Functor (void)
import Peras.Conformance.Test.Prototype (prop_node)
import Test.Hspec (Spec, describe)
import Test.Hspec.QuickCheck (modifyMaxSuccess, prop)
import Test.QuickCheck (Blind (Blind), Gen, Property, Testable, expectFailure, property)
import Test.QuickCheck.DynamicLogic (DL, anyActions_, forAllDL)
import Test.QuickCheck.Gen.Unsafe (Capture (..), capture)
import Test.QuickCheck.Monadic (PropertyM, assert, monadic')
import Test.QuickCheck.StateModel (Actions, runActions)

-- | Test the prototype against the Agda executable specification.
spec :: Spec
spec =
  modifyMaxSuccess (const 1000)
    $ describe "Prototype node"
      . prop "Simulation respects model"
    $ forAllDL anyActions_ (prop_node . Blind)
