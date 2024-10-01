module Peras.Conformance.ExternalSpec where

import Peras.Conformance.Generators (actionsSizeScaling)
import Peras.Conformance.Test.External (prop_node)
import System.IO (Handle)
import Test.Hspec (Spec, describe)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Blind (Blind), arbitrary, forAll, scale)

-- | Test an external implementation against the Agda executable specification.
spec :: Handle -> Handle -> Spec
spec hReader hWriter =
  describe "External node"
    . prop "Implementation respects Peras protocol"
    $ forAll
      (scale (* actionsSizeScaling) arbitrary)
      (prop_node hReader hWriter . Blind)
