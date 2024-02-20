{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Peras.Node.Netsim where

import Control.Monad.IO.Class (MonadIO)
import Peras.NodeModel (RunMonad)
import Test.QuickCheck (Gen, Property, Testable)
import Test.QuickCheck.Monadic (PropertyM)

newtype Netsim io a = Netsim {runNetSim :: io a}
  deriving (Functor, Applicative, Monad, MonadIO)

runPropInNetSim :: Testable a => PropertyM (RunMonad (Netsim IO)) a -> Gen Property
runPropInNetSim _prop = undefined
