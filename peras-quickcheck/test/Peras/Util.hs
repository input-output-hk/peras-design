{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Peras.Util where

import Control.Monad.Reader (ReaderT (..))
import Control.Monad.State (lift)
import Peras.NetworkModel (RunMonad, Simulator, runMonad)
import Test.QuickCheck.Monadic (PropertyM (..))

-- Stolen from https://github.com/input-output-hk/quickcheck-dynamic/blob/c309099aa30333a34d3f70ad7acc87d033dd5cdc/quickcheck-dynamic/src/Test/QuickCheck/Extras.hs#L7
-- TODO: generalise the combinators in Extra to arbitrary natural transformations ?
runPropInIO :: Monad m => Simulator m -> PropertyM (RunMonad m) a -> PropertyM m a
runPropInIO s0 p = MkPropertyM $ \k -> do
  m <- unPropertyM p $ fmap lift . k
  return $ runReaderT (runMonad m) s0
