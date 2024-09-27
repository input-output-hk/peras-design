module Peras.Conformance.TestSpec where

import Peras.Conformance.Generators (actionsSizeScaling)
import Peras.Conformance.Test.Prototype (prop_node)
import Test.Hspec (Spec, describe)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Blind (Blind), arbitrary, forAll, scale)

-- | Test the prototype against the Agda executable specification.
spec :: Spec
spec =
  describe "Prototype node"
    . prop "Simulation respects model"
    $ forAll
      (scale (* actionsSizeScaling) arbitrary)
      (prop_node . Blind)
