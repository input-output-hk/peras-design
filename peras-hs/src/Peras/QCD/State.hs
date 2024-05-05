{-# LANGUAGE RankNTypes #-}

module Peras.QCD.State where

import Control.Lens (Getting, assign, modifying)
import qualified Control.Lens as L (Lens', use)
import Control.Monad.State (MonadState)
import qualified Control.Monad.State as S (State)

type State s a = S.State s a

type Lens' s a = L.Lens' s a

lens' :: (s -> a) -> (s -> a -> s) -> Lens' s a
lens' sa sbt afb s = sbt s <$> afb (sa s)

use :: MonadState s m => Getting a s a -> m a
use = L.use

(≔) :: Lens' s a -> a -> State s ()
(≔) = assign

(≕) :: Lens' s a -> (a -> a) -> State s ()
(≕) = modifying
