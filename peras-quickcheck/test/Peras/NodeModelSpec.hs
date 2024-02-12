{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Peras.NodeModelSpec where

import Control.Monad.IOSim (IOSim, runSimTrace, selectTraceEventsSayWithTime', traceResult)
import Control.Monad.Reader (ReaderT (runReaderT))
import Data.Functor (void)
import Peras.Message (NodeId (..))
import Peras.NodeModel (Action (..), Node (..), NodeModel (..), RunMonad, initialiseNodeEnv, runMonad)
import Test.Hspec (Spec)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Gen, Property, Testable, counterexample, property, within)
import Test.QuickCheck.DynamicLogic (DL, action, anyActions_, forAllDL, getModelStateDL)
import Test.QuickCheck.Gen.Unsafe (Capture (..), capture)
import Test.QuickCheck.Monadic (PropertyM (..), assert, monadic')
import Test.QuickCheck.StateModel (Actions, runActions)

spec :: Spec
spec =
  prop "Honnest node mints blocks according to stakes" propHonestNodeMintingRate

propHonestNodeMintingRate :: Property
propHonestNodeMintingRate =
  within 5000000 $
    forAllDL chainProgress propNodeModel

chainProgress :: DL NodeModel ()
chainProgress = do
  anyActions_
  getModelStateDL >>= \NodeModel{forgedBlocks} ->
    void $ action (ForgedBlocksRespectSchedule forgedBlocks)

propNodeModel :: Actions NodeModel -> Property
propNodeModel actions =
  property $
    runPropInIOSim $ do
      _ <- runActions actions
      assert True

runPropInIOSim :: Testable a => (forall s. PropertyM (RunMonad (IOSim s)) a) -> Gen Property
runPropInIOSim p = do
  Capture eval <- capture
  let simTrace =
        runSimTrace $
          initialiseNodeEnv
            >>= (runReaderT (runMonad $ eval $ monadic' p) . Node (MkNodeId "N1"))
      traceDump = map (\(t, s) -> show t <> " : " <> s) $ selectTraceEventsSayWithTime' simTrace
      logsOnError = counterexample ("trace:\n" <> unlines traceDump)
  case traceResult False simTrace of
    Right x ->
      pure $ logsOnError x
    Left ex ->
      pure $ counterexample (show ex) $ logsOnError $ property False
