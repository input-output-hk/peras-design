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

module MAlonzo.Code.Agda.Builtin.FromNat where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
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

-- Agda.Builtin.FromNat.Number
d_Number_10 a0 a1 = ()
newtype T_Number_10
  = C_Number'46'constructor_55 (Integer -> AgdaAny -> AgdaAny)

-- Agda.Builtin.FromNat.Number.Constraint
d_Constraint_24 :: T_Number_10 -> Integer -> ()
d_Constraint_24 = erased

-- Agda.Builtin.FromNat.Number.fromNat
d_fromNat_30 :: T_Number_10 -> Integer -> AgdaAny -> AgdaAny
d_fromNat_30 v0 =
  case coe v0 of
    C_Number'46'constructor_55 v2 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Agda.Builtin.FromNat._.fromNat
d_fromNat_34 :: T_Number_10 -> Integer -> AgdaAny -> AgdaAny
d_fromNat_34 v0 = coe d_fromNat_30 (coe v0)