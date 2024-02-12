{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Peras.Util where

import Control.Monad.IOSim (IOSim, runSimTrace, selectTraceEventsSayWithTime', traceResult)
import Control.Monad.State (evalStateT, get, lift)
import Peras.NetworkModel (Nodes (..), RunMonad, nodes, runMonad)
import Test.QuickCheck (Gen, Property, Testable, counterexample, property)
import Test.QuickCheck.Gen.Unsafe (Capture (..), capture)
import Test.QuickCheck.Monadic (PropertyM (..), monadic', run)

-- Stolen from https://github.com/input-output-hk/quickcheck-dynamic/blob/c309099aa30333a34d3f70ad7acc87d033dd5cdc/quickcheck-dynamic/src/Test/QuickCheck/Extras.hs#L7
-- TODO: generalise the combinators in Extra to arbitrary natural transformations ?
runPropInIO :: Monad m => Nodes m -> PropertyM (RunMonad m) a -> PropertyM m (a, Nodes m)
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

runPropInIOSim :: Testable a => (forall s. PropertyM (RunMonad (IOSim s)) a) -> Gen Property
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
