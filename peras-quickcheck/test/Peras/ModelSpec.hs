{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Peras.ModelSpec where

import Control.Monad (forM_)
import Control.Monad.IOSim (IOSim, runSimTrace, selectTraceEventsSayWithTime', traceResult)
import Control.Monad.State (evalStateT, get, lift)
import Peras.Model (Action (..), Network (..), Nodes (..), RunMonad, nodes, runMonad)
import Test.Hspec (Spec)
import Test.Hspec.QuickCheck (modifyMaxShrinks, prop)
import Test.QuickCheck (Gen, Property, Testable, counterexample, property, verbose, within)
import Test.QuickCheck.DynamicLogic (DL, action, anyActions_, forAllDL, getModelStateDL)
import Test.QuickCheck.Gen.Unsafe (Capture (..), capture)
import Test.QuickCheck.Monadic (PropertyM (..), assert, monadic', monadicIO, run)
import Test.QuickCheck.StateModel (Actions, runActions)

spec :: Spec
spec =
  modifyMaxShrinks (const 0) $ prop "Chain progress" prop_chain_progress

prop_chain_progress :: Property
prop_chain_progress =
  within 5000000 $
    forAllDL chainProgress prop_HydraModel

chainProgress :: DL Network ()
chainProgress = do
  anyActions_
  getModelStateDL >>= \Network{nodeIds} ->
    forM_ nodeIds (action . ObserveBestChain)

prop_HydraModel :: Actions Network -> Property
prop_HydraModel actions =
  property $
    runPropInIOSim $ do
      _ <- runActions actions
      assert True

-- Stolen from https://github.com/input-output-hk/quickcheck-dynamic/blob/c309099aa30333a34d3f70ad7acc87d033dd5cdc/quickcheck-dynamic/src/Test/QuickCheck/Extras.hs#L7
-- TODO: generalise the combinators in Extra to arbitrary natural transformations ?
runPropInIO :: (Monad m) => Nodes m -> PropertyM (RunMonad m) a -> PropertyM m (a, Nodes m)
runPropInIO s0 p = MkPropertyM $ \k -> do
  m <-
    unPropertyM
      ( do
          a <- p
          s <- run get
          return (a, s)
      )
      $ fmap lift . k
  return $ evalStateT (runMonad m) s0

runPropInIOSim :: (Testable a) => (forall s. PropertyM (RunMonad (IOSim s)) a) -> Gen Property
runPropInIOSim p = do
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
