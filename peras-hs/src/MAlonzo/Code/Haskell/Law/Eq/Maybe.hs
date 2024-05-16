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

module MAlonzo.Code.Haskell.Law.Eq.Maybe where

import qualified Data.Text
import qualified MAlonzo.Code.Haskell.Law.Eq.Def
import qualified MAlonzo.Code.Haskell.Law.Equality
import qualified MAlonzo.Code.Haskell.Prim.Eq
import qualified MAlonzo.Code.Haskell.Prim.Maybe
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

-- Haskell.Law.Eq.Maybe.reflectsJust
d_reflectsJust_14 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  MAlonzo.Code.Haskell.Law.Eq.Def.T_IsLawfulEq_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Haskell.Law.Equality.T_Reflects_118
d_reflectsJust_14 ~v0 v1 ~v2 v3 v4 = du_reflectsJust_14 v1 v3 v4
du_reflectsJust_14 ::
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Haskell.Law.Equality.T_Reflects_118
du_reflectsJust_14 v0 v1 v2 =
  let v3 =
        coe MAlonzo.Code.Haskell.Prim.Eq.d__'61''61'__14 v0 v1 v2
   in coe
        ( if coe v3
            then coe MAlonzo.Code.Haskell.Law.Equality.C_ofY_126 erased
            else coe MAlonzo.Code.Haskell.Law.Equality.C_ofN_130
        )

-- Haskell.Law.Eq.Maybe.iLawfulEqMaybe
d_iLawfulEqMaybe_38 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  MAlonzo.Code.Haskell.Law.Eq.Def.T_IsLawfulEq_12 ->
  MAlonzo.Code.Haskell.Law.Eq.Def.T_IsLawfulEq_12
d_iLawfulEqMaybe_38 ~v0 v1 ~v2 = du_iLawfulEqMaybe_38 v1
du_iLawfulEqMaybe_38 ::
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  MAlonzo.Code.Haskell.Law.Eq.Def.T_IsLawfulEq_12
du_iLawfulEqMaybe_38 v0 =
  coe
    MAlonzo.Code.Haskell.Law.Eq.Def.C_IsLawfulEq'46'constructor_169
    ( coe
        ( \v1 ->
            case coe v1 of
              MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16 ->
                coe
                  ( \v2 ->
                      case coe v2 of
                        MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16 ->
                          coe MAlonzo.Code.Haskell.Law.Equality.C_ofY_126 erased
                        MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 v3 ->
                          coe MAlonzo.Code.Haskell.Law.Equality.C_ofN_130
                        _ -> MAlonzo.RTE.mazUnreachableError
                  )
              MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 v2 ->
                coe
                  ( \v3 ->
                      case coe v3 of
                        MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16 ->
                          coe MAlonzo.Code.Haskell.Law.Equality.C_ofN_130
                        MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 v4 ->
                          coe du_reflectsJust_14 (coe v0) (coe v2) (coe v4)
                        _ -> MAlonzo.RTE.mazUnreachableError
                  )
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )
