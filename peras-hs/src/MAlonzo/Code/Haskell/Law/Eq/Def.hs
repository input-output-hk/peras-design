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

module MAlonzo.Code.Haskell.Law.Eq.Def where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Haskell.Law.Equality
import qualified MAlonzo.Code.Haskell.Prim
import qualified MAlonzo.Code.Haskell.Prim.Eq
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

-- Haskell.Law.Eq.Def.IsLawfulEq
d_IsLawfulEq_12 a0 a1 = ()
newtype T_IsLawfulEq_12
  = C_IsLawfulEq'46'constructor_169
      ( AgdaAny ->
        AgdaAny ->
        MAlonzo.Code.Haskell.Law.Equality.T_Reflects_118
      )

-- Haskell.Law.Eq.Def.IsLawfulEq.isEquality
d_isEquality_28 ::
  T_IsLawfulEq_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Haskell.Law.Equality.T_Reflects_118
d_isEquality_28 v0 =
  case coe v0 of
    C_IsLawfulEq'46'constructor_169 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Law.Eq.Def.IsLawfulEq.equality
d_equality_34 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  T_IsLawfulEq_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_equality_34 = erased

-- Haskell.Law.Eq.Def.IsLawfulEq.nequality
d_nequality_46 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  T_IsLawfulEq_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Haskell.Prim.T_'8869'_90
d_nequality_46 = erased

-- Haskell.Law.Eq.Def.IsLawfulEq.equality'
d_equality''_58 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  T_IsLawfulEq_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_equality''_58 = erased

-- Haskell.Law.Eq.Def.IsLawfulEq.nequality'
d_nequality''_88 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  T_IsLawfulEq_12 ->
  AgdaAny ->
  AgdaAny ->
  ( MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Haskell.Prim.T_'8869'_90
  ) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nequality''_88 = erased

-- Haskell.Law.Eq.Def._.equality
d_equality_116 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  T_IsLawfulEq_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_equality_116 = erased

-- Haskell.Law.Eq.Def._.equality'
d_equality''_118 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  T_IsLawfulEq_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_equality''_118 = erased

-- Haskell.Law.Eq.Def._.isEquality
d_isEquality_120 ::
  T_IsLawfulEq_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Haskell.Law.Equality.T_Reflects_118
d_isEquality_120 v0 = coe d_isEquality_28 (coe v0)

-- Haskell.Law.Eq.Def._.nequality
d_nequality_122 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  T_IsLawfulEq_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Haskell.Prim.T_'8869'_90
d_nequality_122 = erased

-- Haskell.Law.Eq.Def._.nequality'
d_nequality''_124 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  T_IsLawfulEq_12 ->
  AgdaAny ->
  AgdaAny ->
  ( MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Haskell.Prim.T_'8869'_90
  ) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nequality''_124 = erased

-- Haskell.Law.Eq.Def.eqReflexivity
d_eqReflexivity_130 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  T_IsLawfulEq_12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eqReflexivity_130 = erased

-- Haskell.Law.Eq.Def.eqSymmetry
d_eqSymmetry_140 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  T_IsLawfulEq_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eqSymmetry_140 = erased

-- Haskell.Law.Eq.Def.eqTransitivity
d_eqTransitivity_170 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  T_IsLawfulEq_12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eqTransitivity_170 = erased

-- Haskell.Law.Eq.Def.eqExtensionality
d_eqExtensionality_192 ::
  () ->
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  T_IsLawfulEq_12 ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  T_IsLawfulEq_12 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eqExtensionality_192 = erased

-- Haskell.Law.Eq.Def.eqNegation
d_eqNegation_208 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  T_IsLawfulEq_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eqNegation_208 = erased

-- Haskell.Law.Eq.Def.iLawfulEqNat
d_iLawfulEqNat_210 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Eq.Def.iLawfulEqNat"

-- Haskell.Law.Eq.Def.iLawfulEqInteger
d_iLawfulEqInteger_212 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Eq.Def.iLawfulEqInteger"

-- Haskell.Law.Eq.Def.iLawfulEqInt
d_iLawfulEqInt_214 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Eq.Def.iLawfulEqInt"

-- Haskell.Law.Eq.Def.iLawfulEqWord
d_iLawfulEqWord_216 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Eq.Def.iLawfulEqWord"

-- Haskell.Law.Eq.Def.iLawfulEqDouble
d_iLawfulEqDouble_218 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Eq.Def.iLawfulEqDouble"

-- Haskell.Law.Eq.Def.iLawfulEqChar
d_iLawfulEqChar_220 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Eq.Def.iLawfulEqChar"

-- Haskell.Law.Eq.Def.iLawfulEqUnit
d_iLawfulEqUnit_222 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Eq.Def.iLawfulEqUnit"

-- Haskell.Law.Eq.Def.iLawfulEqTuple₂
d_iLawfulEqTuple'8322'_228 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Eq.Def.iLawfulEqTuple\8322"

-- Haskell.Law.Eq.Def.iLawfulEqTuple₃
d_iLawfulEqTuple'8323'_236 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Eq.Def.iLawfulEqTuple\8323"

-- Haskell.Law.Eq.Def.iLawfulEqList
d_iLawfulEqList_240 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Eq.Def.iLawfulEqList"

-- Haskell.Law.Eq.Def.iLawfulEqEither
d_iLawfulEqEither_246 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Eq.Def.iLawfulEqEither"
