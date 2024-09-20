module Peras.Conformance.TestNewSpec where

import Peras.Conformance.Generators (actionsSizeScaling)
import Peras.Conformance.TestNew.Prototype (prop_node)
import Test.Hspec (Spec, describe)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (
  Arbitrary (arbitrary),
  Blind (Blind),
  forAll,
  scale,
 )

-- | Test the prototype against the Agda executable specification.
spec :: Spec
spec =
  describe "Prototype node"
    . prop "Simulation respects model"
    $ forAll
      (scale (* actionsSizeScaling) arbitrary)
      (prop_node . Blind)
