{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Peras.Markov.Class (
  Half (..),
) where

import NumericPrelude.Base (($))
import NumericPrelude.Numeric
import Peras.Markov.Polynomial (Polynomial, num)

import qualified Algebra.Field as Field (C)

class Half a where
  half :: a

instance Half Double where
  half = 1 / 2

instance Half Rational where
  half = 1 % 2

instance Field.C a => Half (Polynomial a) where
  half = num $ one / (one + one)
