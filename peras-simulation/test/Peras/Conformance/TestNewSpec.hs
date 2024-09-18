module Peras.Conformance.TestNewSpec where

import Control.Monad (replicateM_, (>>))
import Control.Monad.State (evalStateT)
import Data.Default (def)
import Data.Functor (void)
import Peras.Conformance.TestNew.Prototype (prop_node)
import Test.Hspec (Spec, describe)
import Test.Hspec.QuickCheck (modifyMaxSuccess, prop)
import Test.QuickCheck (Blind (Blind), Gen, Property, Testable, arbitrary, expectFailure, forAll, property, resize)
import Test.QuickCheck.DynamicLogic (DL, anyAction, anyActions_, forAllDL)
import Test.QuickCheck.Gen.Unsafe (Capture (..), capture)
import Test.QuickCheck.Monadic (PropertyM, assert, monadic')
import Test.QuickCheck.StateModel (Actions, runActions)

-- | Test the prototype against the Agda executable specification.
spec :: Spec
spec =
  describe "Prototype node"
    . prop "Simulation respects model"
    $ (if True then forAllDL anyActions_ else forAll arbitrary)
      (prop_node . Blind)
