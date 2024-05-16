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

module MAlonzo.Code.Haskell.Law.Equality where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Haskell.Prim
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

-- Haskell.Law.Equality._≠_
d__'8800'__8 :: () -> AgdaAny -> AgdaAny -> ()
d__'8800'__8 = erased

-- Haskell.Law.Equality.cong
d_cong_24 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong_24 = erased

-- Haskell.Law.Equality.cong₂
d_cong'8322'_38 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong'8322'_38 = erased

-- Haskell.Law.Equality.sym
d_sym_48 ::
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_48 = erased

-- Haskell.Law.Equality.trans
d_trans_58 ::
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_58 = erased

-- Haskell.Law.Equality.trustMe
d_trustMe_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trustMe_68 = erased

-- Haskell.Law.Equality.begin_
d_begin__74 ::
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_begin__74 = erased

-- Haskell.Law.Equality._≡⟨⟩_
d__'8801''10216''10217'__82 ::
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d__'8801''10216''10217'__82 = erased

-- Haskell.Law.Equality.step-≡
d_step'45''8801'_92 ::
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45''8801'_92 = erased

-- Haskell.Law.Equality.step-≡˘
d_step'45''8801''728'_104 ::
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45''8801''728'_104 = erased

-- Haskell.Law.Equality._∎
d__'8718'_112 ::
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d__'8718'_112 = erased

-- Haskell.Law.Equality.Reflects
d_Reflects_118 a0 a1 a2 = ()
data T_Reflects_118 = C_ofY_126 AgdaAny | C_ofN_130

-- Haskell.Law.Equality.of
d_of_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Bool ->
  AgdaAny ->
  T_Reflects_118
d_of_138 ~v0 ~v1 v2 v3 = du_of_138 v2 v3
du_of_138 :: Bool -> AgdaAny -> T_Reflects_118
du_of_138 v0 v1 =
  if coe v0 then coe C_ofY_126 (coe v1) else coe C_ofN_130

-- Haskell.Law.Equality.invert
d_invert_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Bool ->
  T_Reflects_118 ->
  AgdaAny
d_invert_146 ~v0 ~v1 ~v2 v3 = du_invert_146 v3
du_invert_146 :: T_Reflects_118 -> AgdaAny
du_invert_146 v0 =
  case coe v0 of
    C_ofY_126 v1 -> coe v1
    C_ofN_130 -> erased
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Law.Equality.extractTrue
d_extractTrue_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Reflects_118 ->
  AgdaAny
d_extractTrue_156 ~v0 ~v1 ~v2 ~v3 v4 = du_extractTrue_156 v4
du_extractTrue_156 :: T_Reflects_118 -> AgdaAny
du_extractTrue_156 v0 =
  case coe v0 of
    C_ofY_126 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Law.Equality.extractFalse
d_extractFalse_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Reflects_118 ->
  AgdaAny ->
  MAlonzo.Code.Haskell.Prim.T_'8869'_90
d_extractFalse_164 = erased
