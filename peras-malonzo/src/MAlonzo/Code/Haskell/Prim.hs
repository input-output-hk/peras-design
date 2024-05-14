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

module MAlonzo.Code.Haskell.Prim where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.FromNat
import qualified MAlonzo.Code.Agda.Builtin.FromString
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

-- Haskell.Prim.id
d_id_24 :: () -> AgdaAny -> AgdaAny
d_id_24 ~v0 v1 = du_id_24 v1
du_id_24 :: AgdaAny -> AgdaAny
du_id_24 v0 = coe v0

-- Haskell.Prim._∘_
d__'8728'__28 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
d__'8728'__28 ~v0 ~v1 ~v2 v3 v4 v5 = du__'8728'__28 v3 v4 v5
du__'8728'__28 ::
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'8728'__28 v0 v1 v2 = coe v0 (coe v1 v2)

-- Haskell.Prim.flip
d_flip_36 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d_flip_36 ~v0 ~v1 ~v2 v3 v4 v5 = du_flip_36 v3 v4 v5
du_flip_36 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_flip_36 v0 v1 v2 = coe v0 v2 v1

-- Haskell.Prim.const
d_const_44 :: () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_const_44 ~v0 ~v1 v2 ~v3 = du_const_44 v2
du_const_44 :: AgdaAny -> AgdaAny
du_const_44 v0 = coe v0

-- Haskell.Prim._$_
d__'36'__48 ::
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'36'__48 ~v0 ~v1 v2 v3 = du__'36'__48 v2 v3
du__'36'__48 :: (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'36'__48 v0 v1 = coe v0 v1

-- Haskell.Prim.case_of_
d_case_of__58 ::
  () ->
  () ->
  AgdaAny ->
  ( AgdaAny ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    AgdaAny
  ) ->
  AgdaAny
d_case_of__58 ~v0 ~v1 v2 v3 = du_case_of__58 v2 v3
du_case_of__58 ::
  AgdaAny ->
  ( AgdaAny ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    AgdaAny
  ) ->
  AgdaAny
du_case_of__58 v0 v1 = coe v1 v0 erased

-- Haskell.Prim.if_then_else_
d_if_then_else__68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  AgdaAny
d_if_then_else__68 ~v0 ~v1 v2 v3 v4 = du_if_then_else__68 v2 v3 v4
du_if_then_else__68 ::
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  AgdaAny
du_if_then_else__68 v0 v1 v2 =
  if coe v0 then coe v1 erased else coe v2 erased

-- Haskell.Prim.iIsStringAgdaString
d_iIsStringAgdaString_78 ::
  MAlonzo.Code.Agda.Builtin.FromString.T_IsString_10
d_iIsStringAgdaString_78 =
  coe
    MAlonzo.Code.Agda.Builtin.FromString.C_IsString'46'constructor_37
    (\v0 v1 -> v0)

-- Haskell.Prim.iNumberNat
d_iNumberNat_82 :: MAlonzo.Code.Agda.Builtin.FromNat.T_Number_10
d_iNumberNat_82 =
  coe
    MAlonzo.Code.Agda.Builtin.FromNat.C_Number'46'constructor_55
    (\v0 v1 -> v0)

-- Haskell.Prim.lengthNat
d_lengthNat_86 :: () -> [AgdaAny] -> Integer
d_lengthNat_86 ~v0 v1 = du_lengthNat_86 v1
du_lengthNat_86 :: [AgdaAny] -> Integer
du_lengthNat_86 v0 =
  case coe v0 of
    [] -> coe (0 :: Integer)
    (:) v1 v2 ->
      coe addInt (coe (1 :: Integer)) (coe du_lengthNat_86 (coe v2))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.⊥
d_'8869'_90 = ()
data T_'8869'_90

-- Haskell.Prim.magic
d_magic_94 :: () -> T_'8869'_90 -> AgdaAny
d_magic_94 ~v0 ~v1 = du_magic_94
du_magic_94 :: AgdaAny
du_magic_94 = MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.All
d_All_104 a0 a1 a2 a3 a4 = ()
data T_All_104 = C_allNil_114 | C_allCons_124 AgdaAny T_All_104

-- Haskell.Prim.IsTrue
d_IsTrue_126 a0 = ()
data T_IsTrue_126 = C_itsTrue_128

-- Haskell.Prim.IsFalse
d_IsFalse_130 a0 = ()
data T_IsFalse_130 = C_itsFalse_132

-- Haskell.Prim.NonEmpty
d_NonEmpty_136 a0 a1 = ()
data T_NonEmpty_136 = C_itsNonEmpty_144

-- Haskell.Prim.TypeError
d_TypeError_148 a0 = ()
data T_TypeError_148

-- Haskell.Prim.it
d_it_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
d_it_156 ~v0 ~v1 v2 = du_it_156 v2
du_it_156 :: AgdaAny -> AgdaAny
du_it_156 v0 = coe v0
