{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Haskell.Prim.Double where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Float
import qualified MAlonzo.Code.Agda.Builtin.FromNat
import qualified MAlonzo.Code.Agda.Builtin.FromNeg
import MAlonzo.RTE (
  AgdaAny,
  add64,
  addInt,
  coe,
  eq64,
  eqInt,
  erased,
  geqInt,
  lt64,
  ltInt,
  mul64,
  mulInt,
  quot64,
  quotInt,
  rem64,
  remInt,
  sub64,
  subInt,
  word64FromNat,
  word64ToNat,
 )
import qualified MAlonzo.RTE

-- Haskell.Prim.Double.iNumberDouble
d_iNumberDouble_6 :: MAlonzo.Code.Agda.Builtin.FromNat.T_Number_10
d_iNumberDouble_6 =
  coe
    MAlonzo.Code.Agda.Builtin.FromNat.C_Number'46'constructor_55
    ( \v0 v1 ->
        coe MAlonzo.Code.Agda.Builtin.Float.d_primNatToFloat_24 v0
    )

-- Haskell.Prim.Double.iNegativeDouble
d_iNegativeDouble_10 ::
  MAlonzo.Code.Agda.Builtin.FromNeg.T_Negative_10
d_iNegativeDouble_10 =
  coe
    MAlonzo.Code.Agda.Builtin.FromNeg.C_Negative'46'constructor_55
    ( \v0 v1 ->
        coe
          MAlonzo.Code.Agda.Builtin.Float.d_primFloatMinus_50
          (0.0 :: Double)
          (coe MAlonzo.Code.Agda.Builtin.Float.d_primNatToFloat_24 v0)
    )
