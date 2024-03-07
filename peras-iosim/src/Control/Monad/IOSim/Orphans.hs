{-# OPTIONS_GHC -fno-warn-orphans #-}

module Control.Monad.IOSim.Orphans (

) where

import Control.Monad.Class.MonadSay (MonadSay (..))
import Control.Monad.Except (ExceptT)
import Control.Monad.State (StateT, lift)

instance MonadSay m => MonadSay (ExceptT e m) where
  say = lift . say

instance MonadSay m => MonadSay (StateT s m) where
  say = lift . say
