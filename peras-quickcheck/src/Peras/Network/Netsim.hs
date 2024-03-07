module Peras.Network.Netsim where

import Peras.NetworkModel (RunMonad)
import Test.QuickCheck (Property, Testable, ioProperty)
import Test.QuickCheck.Monadic (PropertyM, monadic)

runPropInNetSim :: Testable a => PropertyM (RunMonad IO) a -> Property
runPropInNetSim = monadic (ioProperty . runner)
 where
  runner :: RunMonad IO Property -> IO Property
  runner = undefined
