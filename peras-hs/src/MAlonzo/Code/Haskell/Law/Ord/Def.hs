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

module MAlonzo.Code.Haskell.Law.Ord.Def where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Haskell.Law.Eq.Def
import qualified MAlonzo.Code.Haskell.Prim.Ord
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

-- Haskell.Law.Ord.Def.IsLawfulOrd
d_IsLawfulOrd_12 a0 a1 = ()
newtype T_IsLawfulOrd_12
  = C_IsLawfulOrd'46'constructor_7911 MAlonzo.Code.Haskell.Law.Eq.Def.T_IsLawfulEq_12

-- Haskell.Law.Ord.Def.IsLawfulOrd.super
d_super_92 ::
  T_IsLawfulOrd_12 -> MAlonzo.Code.Haskell.Law.Eq.Def.T_IsLawfulEq_12
d_super_92 v0 =
  case coe v0 of
    C_IsLawfulOrd'46'constructor_7911 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Law.Ord.Def.IsLawfulOrd.comparability
d_comparability_98 ::
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comparability_98 = erased

-- Haskell.Law.Ord.Def.IsLawfulOrd.transitivity
d_transitivity_106 ::
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_transitivity_106 = erased

-- Haskell.Law.Ord.Def.IsLawfulOrd.reflexivity
d_reflexivity_110 ::
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexivity_110 = erased

-- Haskell.Law.Ord.Def.IsLawfulOrd.antisymmetry
d_antisymmetry_116 ::
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antisymmetry_116 = erased

-- Haskell.Law.Ord.Def.IsLawfulOrd.lte2gte
d_lte2gte_122 ::
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lte2gte_122 = erased

-- Haskell.Law.Ord.Def.IsLawfulOrd.lt2LteNeq
d_lt2LteNeq_128 ::
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lt2LteNeq_128 = erased

-- Haskell.Law.Ord.Def.IsLawfulOrd.lt2gt
d_lt2gt_134 ::
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lt2gt_134 = erased

-- Haskell.Law.Ord.Def.IsLawfulOrd.compareLt
d_compareLt_140 ::
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compareLt_140 = erased

-- Haskell.Law.Ord.Def.IsLawfulOrd.compareGt
d_compareGt_146 ::
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compareGt_146 = erased

-- Haskell.Law.Ord.Def.IsLawfulOrd.compareEq
d_compareEq_152 ::
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compareEq_152 = erased

-- Haskell.Law.Ord.Def.IsLawfulOrd.min2if
d_min2if_158 ::
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_min2if_158 = erased

-- Haskell.Law.Ord.Def.IsLawfulOrd.max2if
d_max2if_164 ::
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_max2if_164 = erased

-- Haskell.Law.Ord.Def._.antisymmetry
d_antisymmetry_168 ::
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antisymmetry_168 = erased

-- Haskell.Law.Ord.Def._.comparability
d_comparability_170 ::
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comparability_170 = erased

-- Haskell.Law.Ord.Def._.compareEq
d_compareEq_172 ::
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compareEq_172 = erased

-- Haskell.Law.Ord.Def._.compareGt
d_compareGt_174 ::
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compareGt_174 = erased

-- Haskell.Law.Ord.Def._.compareLt
d_compareLt_176 ::
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compareLt_176 = erased

-- Haskell.Law.Ord.Def._.lt2LteNeq
d_lt2LteNeq_178 ::
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lt2LteNeq_178 = erased

-- Haskell.Law.Ord.Def._.lt2gt
d_lt2gt_180 ::
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lt2gt_180 = erased

-- Haskell.Law.Ord.Def._.lte2gte
d_lte2gte_182 ::
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lte2gte_182 = erased

-- Haskell.Law.Ord.Def._.max2if
d_max2if_184 ::
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_max2if_184 = erased

-- Haskell.Law.Ord.Def._.min2if
d_min2if_186 ::
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_min2if_186 = erased

-- Haskell.Law.Ord.Def._.reflexivity
d_reflexivity_188 ::
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexivity_188 = erased

-- Haskell.Law.Ord.Def._.super
d_super_190 ::
  T_IsLawfulOrd_12 -> MAlonzo.Code.Haskell.Law.Eq.Def.T_IsLawfulEq_12
d_super_190 v0 = coe d_super_92 (coe v0)

-- Haskell.Law.Ord.Def._.transitivity
d_transitivity_192 ::
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_transitivity_192 = erased

-- Haskell.Law.Ord.Def.eq2nlt
d_eq2nlt_200 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eq2nlt_200 = erased

-- Haskell.Law.Ord.Def.eq2ngt
d_eq2ngt_226 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eq2ngt_226 = erased

-- Haskell.Law.Ord.Def.gte2GtEq
d_gte2GtEq_252 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gte2GtEq_252 = erased

-- Haskell.Law.Ord.Def.gte2nlt
d_gte2nlt_264 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gte2nlt_264 = erased

-- Haskell.Law.Ord.Def.gte2nLT
d_gte2nLT_292 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gte2nLT_292 = erased

-- Haskell.Law.Ord.Def.lte2LtEq
d_lte2LtEq_312 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lte2LtEq_312 = erased

-- Haskell.Law.Ord.Def.lte2ngt
d_lte2ngt_324 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lte2ngt_324 = erased

-- Haskell.Law.Ord.Def.lte2nGT
d_lte2nGT_352 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lte2nGT_352 = erased

-- Haskell.Law.Ord.Def.eq2lte
d_eq2lte_372 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eq2lte_372 = erased

-- Haskell.Law.Ord.Def.lt2lte
d_lt2lte_394 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lt2lte_394 = erased

-- Haskell.Law.Ord.Def.eq2gte
d_eq2gte_408 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eq2gte_408 = erased

-- Haskell.Law.Ord.Def.gt2gte
d_gt2gte_430 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  T_IsLawfulOrd_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gt2gte_430 = erased

-- Haskell.Law.Ord.Def.iLawfulOrdNat
d_iLawfulOrdNat_450 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Ord.Def.iLawfulOrdNat"

-- Haskell.Law.Ord.Def.iLawfulOrdInteger
d_iLawfulOrdInteger_452 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Ord.Def.iLawfulOrdInteger"

-- Haskell.Law.Ord.Def.iLawfulOrdInt
d_iLawfulOrdInt_454 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Ord.Def.iLawfulOrdInt"

-- Haskell.Law.Ord.Def.iLawfulOrdWord
d_iLawfulOrdWord_456 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Ord.Def.iLawfulOrdWord"

-- Haskell.Law.Ord.Def.iLawfulOrdDouble
d_iLawfulOrdDouble_458 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Ord.Def.iLawfulOrdDouble"

-- Haskell.Law.Ord.Def.iLawfulOrdChar
d_iLawfulOrdChar_460 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Ord.Def.iLawfulOrdChar"

-- Haskell.Law.Ord.Def.iLawfulOrdUnit
d_iLawfulOrdUnit_462 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Ord.Def.iLawfulOrdUnit"

-- Haskell.Law.Ord.Def.iLawfulOrdTuple₂
d_iLawfulOrdTuple'8322'_468 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Ord.Def.iLawfulOrdTuple\8322"

-- Haskell.Law.Ord.Def.iLawfulOrdTuple₃
d_iLawfulOrdTuple'8323'_476 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Ord.Def.iLawfulOrdTuple\8323"

-- Haskell.Law.Ord.Def.iLawfulOrdList
d_iLawfulOrdList_480 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Ord.Def.iLawfulOrdList"

-- Haskell.Law.Ord.Def.iLawfulOrdEither
d_iLawfulOrdEither_486 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Ord.Def.iLawfulOrdEither"
