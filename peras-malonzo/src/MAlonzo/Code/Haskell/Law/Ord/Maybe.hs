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

module MAlonzo.Code.Haskell.Law.Ord.Maybe where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Haskell.Law.Eq.Maybe
import qualified MAlonzo.Code.Haskell.Law.Ord.Def
import qualified MAlonzo.Code.Haskell.Prim.Maybe
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

-- Haskell.Law.Ord.Maybe.compMaybe
d_compMaybe_14 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  MAlonzo.Code.Haskell.Law.Ord.Def.T_IsLawfulOrd_12 ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compMaybe_14 = erased

-- Haskell.Law.Ord.Maybe.transMaybe
d_transMaybe_36 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  MAlonzo.Code.Haskell.Law.Ord.Def.T_IsLawfulOrd_12 ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_transMaybe_36 = erased

-- Haskell.Law.Ord.Maybe.reflMaybe
d_reflMaybe_72 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  MAlonzo.Code.Haskell.Law.Ord.Def.T_IsLawfulOrd_12 ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflMaybe_72 = erased

-- Haskell.Law.Ord.Maybe.antisymmetryMaybe
d_antisymmetryMaybe_86 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  MAlonzo.Code.Haskell.Law.Ord.Def.T_IsLawfulOrd_12 ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antisymmetryMaybe_86 = erased

-- Haskell.Law.Ord.Maybe.lte2gteMaybe
d_lte2gteMaybe_108 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  MAlonzo.Code.Haskell.Law.Ord.Def.T_IsLawfulOrd_12 ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lte2gteMaybe_108 = erased

-- Haskell.Law.Ord.Maybe.lt2LteNeqMaybe
d_lt2LteNeqMaybe_140 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  MAlonzo.Code.Haskell.Law.Ord.Def.T_IsLawfulOrd_12 ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lt2LteNeqMaybe_140 = erased

-- Haskell.Law.Ord.Maybe.lt2gtMaybe
d_lt2gtMaybe_168 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  MAlonzo.Code.Haskell.Law.Ord.Def.T_IsLawfulOrd_12 ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lt2gtMaybe_168 = erased

-- Haskell.Law.Ord.Maybe.compareLtMaybe
d_compareLtMaybe_192 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  MAlonzo.Code.Haskell.Law.Ord.Def.T_IsLawfulOrd_12 ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compareLtMaybe_192 = erased

-- Haskell.Law.Ord.Maybe.compareGtMaybe
d_compareGtMaybe_200 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  MAlonzo.Code.Haskell.Law.Ord.Def.T_IsLawfulOrd_12 ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compareGtMaybe_200 = erased

-- Haskell.Law.Ord.Maybe.compareEqMaybe
d_compareEqMaybe_210 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  MAlonzo.Code.Haskell.Law.Ord.Def.T_IsLawfulOrd_12 ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compareEqMaybe_210 = erased

-- Haskell.Law.Ord.Maybe.min2ifMaybe
d_min2ifMaybe_226 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  MAlonzo.Code.Haskell.Law.Ord.Def.T_IsLawfulOrd_12 ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_min2ifMaybe_226 = erased

-- Haskell.Law.Ord.Maybe.max2ifMaybe
d_max2ifMaybe_242 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  MAlonzo.Code.Haskell.Law.Ord.Def.T_IsLawfulOrd_12 ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_max2ifMaybe_242 = erased

-- Haskell.Law.Ord.Maybe.iLawfulOrdMaybe
d_iLawfulOrdMaybe_258 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  MAlonzo.Code.Haskell.Law.Ord.Def.T_IsLawfulOrd_12 ->
  MAlonzo.Code.Haskell.Law.Ord.Def.T_IsLawfulOrd_12
d_iLawfulOrdMaybe_258 ~v0 v1 ~v2 = du_iLawfulOrdMaybe_258 v1
du_iLawfulOrdMaybe_258 ::
  MAlonzo.Code.Haskell.Prim.Ord.T_Ord_36 ->
  MAlonzo.Code.Haskell.Law.Ord.Def.T_IsLawfulOrd_12
du_iLawfulOrdMaybe_258 v0 =
  coe
    MAlonzo.Code.Haskell.Law.Ord.Def.C_IsLawfulOrd'46'constructor_7911
    ( coe
        MAlonzo.Code.Haskell.Law.Eq.Maybe.du_iLawfulEqMaybe_38
        (coe MAlonzo.Code.Haskell.Prim.Ord.d_super_70 (coe v0))
    )
