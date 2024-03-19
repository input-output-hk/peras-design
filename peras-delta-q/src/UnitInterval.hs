{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module UnitInterval where

class Iops i where
  (<), (<=) :: i -> i -> Bool

  toDouble :: i -> Double

  -- The constraint here is (fromDouble x | x >= 0 && x <= 1)
  fromDouble :: Double -> i

  -- inv x = 1 - x
  inv :: i -> i

  (*) :: i -> i -> i

  -- This is partial function on i with the constraint
  -- (x + y | x <= inv y).  This is because:
  -- x + y <= 1 =
  -- x <= 1 - y
  -- x <= inv y
  (+) :: i -> i -> i

  -- This operation implements (x \/ y = x + y - x*y).
  -- The problem impementing this as above is that (+) and (-)
  -- are partial
  -- functions on i (e.g. 1 + 1 or 0 - 1 are not defined).
  -- However, the operation itself is total on i and can
  -- be implemented in using (*) and (inv) applying De Morgan
  -- like transformation.  Here is why:
  -- For the given (x :: i) and (y :: i)
  --    x' = inv x  (by def) x = 1 - x'
  --    y' = inv y  (by def) y = 1 - y'
  --
  --    x + y - x*y =
  --    (1 - x') + (1 - y') - (1 - x')*(1 - y') =
  --    1 - x' + 1 - y' - (1 - x' - y' + x'*y') =
  --    1 - x' - y' + 1 -  1 + x' + y' - x'*y'  =
  --    1 - x'*y' =
  --    inv (x' * y') =
  --    inv (inv x * inv y)
  (\/) :: i -> i -> i
  x \/ y = inv (inv x UnitInterval.* inv y)

  -- | Upper bound of the unit interval
  one :: i

  -- | Lower bound of the unit interval
  zero :: i

instance Iops Double where
  a < b = a Prelude.< b
  a <= b = a Prelude.<= b
  fromDouble a = a
  toDouble a = a
  inv x = 1 Prelude.- x
  a * b = a Prelude.* b
  a + b = a Prelude.+ b
  one = 1.0
  zero = 0.0

instance Iops Rational where
  a < b = a Prelude.< b
  a <= b = a Prelude.<= b
  inv x = 1 Prelude.- x
  a * b = a Prelude.* b
  a + b = a Prelude.+ b
  fromDouble = toRational
  toDouble = fromRational
  one = 1
  zero = 0
