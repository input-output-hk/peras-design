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

module MAlonzo.Code.Agda.Builtin.FromString where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
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

-- Agda.Builtin.FromString.IsString
d_IsString_10 a0 a1 = ()
newtype T_IsString_10
  = C_IsString'46'constructor_37
      ( MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
        AgdaAny ->
        AgdaAny
      )

-- Agda.Builtin.FromString.IsString.Constraint
d_Constraint_24 ::
  T_IsString_10 -> MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_Constraint_24 = erased

-- Agda.Builtin.FromString.IsString.fromString
d_fromString_30 ::
  T_IsString_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  AgdaAny
d_fromString_30 v0 =
  case coe v0 of
    C_IsString'46'constructor_37 v2 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Agda.Builtin.FromString._.fromString
d_fromString_34 ::
  T_IsString_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  AgdaAny
d_fromString_34 v0 = coe d_fromString_30 (coe v0)
