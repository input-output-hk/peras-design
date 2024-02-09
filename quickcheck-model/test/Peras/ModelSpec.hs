{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}

module Peras.ModelSpec where

import Control.Monad (forM)
import Control.Monad.IOSim (IOSim, runSimTrace, selectTraceEventsSayWithTime', traceResult)
import Control.Monad.State (evalStateT)
import Peras.Model (Action (..), Chain, Network (..), Nodes (..), RunMonad, asList, nodes, runMonad)
import Test.Hspec (Spec)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Gen, Property, Testable, counterexample, property, within)
import Test.QuickCheck.DynamicLogic (DL, action, anyActions_, forAllDL, getModelStateDL)
import qualified Test.QuickCheck.DynamicLogic as DL
import Test.QuickCheck.Gen.Unsafe (Capture (..), capture)
import Test.QuickCheck.Monadic (PropertyM, assert, monadic')
import Test.QuickCheck.StateModel (Actions, Var, runActions)

spec :: Spec
spec =
  prop "Chain progress" prop_chain_progress

prop_chain_progress :: Property
prop_chain_progress =
  within 50000000 $
    forAllDL chainProgress prop_HydraModel

chainProgress :: DL Network ()
chainProgress = do
  anyActions_
  getModelStateDL >>= \Network{nodeIds} -> do
    bestChains <- forM nodeIds (action . ObserveBestChain)
    let (settled, unsettled) = commonPrefix bestChains
    DL.assert "" $
      all (((< 42) . length) . asList) unsettled
        && not (null (asList settled))

commonPrefix :: [Var Chain] -> (Chain, [Chain])
commonPrefix = undefined

prop_HydraModel :: Actions Network -> Property
prop_HydraModel actions = property $
  runIOSimProp $ do
    _ <- runActions actions
    assert True

runIOSimProp :: (Testable a) => (forall s. PropertyM (RunMonad (IOSim s)) a) -> Gen Property
runIOSimProp p = do
  Capture eval <- capture
  let simTrace =
        runSimTrace $
          evalStateT (runMonad $ eval $ monadic' p) nodes
      traceDump = map (\(t, s) -> show t <> " : " <> s) $ selectTraceEventsSayWithTime' simTrace
      logsOnError = counterexample ("trace:\n" <> unlines traceDump)
  case traceResult False simTrace of
    Right x ->
      pure $ logsOnError x
    Left ex ->
      pure $ counterexample (show ex) $ logsOnError $ property False
  where
    nodes = Nodes{nodes = mempty}
