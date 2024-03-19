module Reals where

-- Operations associated to R+
class Rops r where
  fromDouble :: Double -> r
  toDouble :: r -> Double

  (<), (<=)  :: r -> r -> Bool

  -- Total operations
  (+), (*) :: r -> r -> r

  -- Partial minus with the constraint (a - b | a >= b)
  (-) :: r -> r -> r

  (>), (>=) :: r -> r -> Bool
  a >  b = b Reals.<  a
  a >= b = b Reals.<= a

  max, min :: r -> r -> r
  min a b = if a Reals.< b then a else b
  max a b = if a Reals.> b then a else b


-- Trivial instances
instance Rops Double where
  a <  b = a Prelude.<  b
  a <= b = a Prelude.<= b
  a +  b = a Prelude.+ b
  a *  b = a Prelude.* b
  a -  b = a Prelude.- b
  fromDouble a = a
  toDouble a = a
