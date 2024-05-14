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

module MAlonzo.Code.Haskell.Prim.Absurd where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Reflection
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

-- Haskell.Prim.Absurd.refute
d_refute_10 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_refute_10 v0 =
  coe
    MAlonzo.Code.Agda.Builtin.Reflection.C_def_184
    ( coe
        ( MAlonzo.RTE.QName
            (48 :: Integer)
            (16669902008463737155 :: Integer)
            "Haskell.Prim._$_"
            ( MAlonzo.RTE.Fixity
                MAlonzo.RTE.RightAssoc
                (MAlonzo.RTE.Related (0.0 :: Double))
            )
        )
    )
    ( coe
        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
        ( coe
            MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
            ( coe
                MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                ( coe
                    MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                    (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                    (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)
                )
            )
            ( coe
                MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196
                ( coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    ( coe
                        MAlonzo.Code.Agda.Builtin.Reflection.C_absurd'45'clause_278
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                        ( coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            ( coe
                                MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                ( coe
                                    MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                    (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                    ( coe
                                        MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                        (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                        (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)
                                    )
                                )
                                ( coe
                                    MAlonzo.Code.Agda.Builtin.Reflection.C_absurd_264
                                    (coe (0 :: Integer))
                                )
                            )
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                        )
                    )
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                )
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
            )
        )
        ( coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            ( coe
                MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                ( coe
                    MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                    (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                    ( coe
                        MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                        (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                        (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)
                    )
                )
                ( coe
                    MAlonzo.Code.Agda.Builtin.Reflection.C_var_172
                    (coe v0)
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                )
            )
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
        )
    )

-- Haskell.Prim.Absurd.tryRefute
d_tryRefute_14 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  AgdaAny
d_tryRefute_14 v0 v1 =
  case coe v0 of
    0 ->
      coe
        MAlonzo.Code.Agda.Builtin.Reflection.d_typeError_342
        ()
        erased
        ( coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            ( coe
                MAlonzo.Code.Agda.Builtin.Reflection.C_strErr_308
                ( coe
                    ( "No variable of empty type found in the context" ::
                        Data.Text.Text
                    )
                )
            )
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
        )
    _ ->
      let v2 = subInt (coe v0) (coe (1 :: Integer))
       in coe
            ( coe
                MAlonzo.Code.Agda.Builtin.Reflection.d_catchTC_356
                ()
                erased
                ( coe
                    MAlonzo.Code.Agda.Builtin.Reflection.d_unify_336
                    v1
                    (d_refute_10 (coe v2))
                )
                (d_tryRefute_14 (coe v2) (coe v1))
            )

-- Haskell.Prim.Absurd.absurd
d_absurd_20 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_absurd_20 v0 =
  coe
    MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_334
    ()
    ()
    erased
    erased
    MAlonzo.Code.Agda.Builtin.Reflection.d_getContext_374
    ( \v1 ->
        d_tryRefute_14
          (coe MAlonzo.Code.Haskell.Prim.du_lengthNat_86 (coe v1))
          (coe v0)
    )
