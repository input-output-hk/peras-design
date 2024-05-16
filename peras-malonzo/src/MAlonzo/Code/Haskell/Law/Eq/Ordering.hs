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

module MAlonzo.Code.Haskell.Law.Eq.Ordering where

import qualified Data.Text
import qualified MAlonzo.Code.Haskell.Law.Eq.Def
import qualified MAlonzo.Code.Haskell.Law.Equality
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

-- Haskell.Law.Eq.Ordering.iLawfulEqOrdering
d_iLawfulEqOrdering_8 ::
  MAlonzo.Code.Haskell.Law.Eq.Def.T_IsLawfulEq_12
d_iLawfulEqOrdering_8 =
  coe
    MAlonzo.Code.Haskell.Law.Eq.Def.C_IsLawfulEq'46'constructor_169
    ( coe
        ( \v0 ->
            case coe v0 of
              MAlonzo.Code.Haskell.Prim.Ord.C_LT_8 ->
                coe
                  ( \v1 ->
                      case coe v1 of
                        MAlonzo.Code.Haskell.Prim.Ord.C_LT_8 ->
                          coe MAlonzo.Code.Haskell.Law.Equality.C_ofY_126 erased
                        MAlonzo.Code.Haskell.Prim.Ord.C_EQ_10 ->
                          coe MAlonzo.Code.Haskell.Law.Equality.C_ofN_130
                        MAlonzo.Code.Haskell.Prim.Ord.C_GT_12 ->
                          coe MAlonzo.Code.Haskell.Law.Equality.C_ofN_130
                        _ -> MAlonzo.RTE.mazUnreachableError
                  )
              MAlonzo.Code.Haskell.Prim.Ord.C_EQ_10 ->
                coe
                  ( \v1 ->
                      case coe v1 of
                        MAlonzo.Code.Haskell.Prim.Ord.C_LT_8 ->
                          coe MAlonzo.Code.Haskell.Law.Equality.C_ofN_130
                        MAlonzo.Code.Haskell.Prim.Ord.C_EQ_10 ->
                          coe MAlonzo.Code.Haskell.Law.Equality.C_ofY_126 erased
                        MAlonzo.Code.Haskell.Prim.Ord.C_GT_12 ->
                          coe MAlonzo.Code.Haskell.Law.Equality.C_ofN_130
                        _ -> MAlonzo.RTE.mazUnreachableError
                  )
              MAlonzo.Code.Haskell.Prim.Ord.C_GT_12 ->
                coe
                  ( \v1 ->
                      case coe v1 of
                        MAlonzo.Code.Haskell.Prim.Ord.C_LT_8 ->
                          coe MAlonzo.Code.Haskell.Law.Equality.C_ofN_130
                        MAlonzo.Code.Haskell.Prim.Ord.C_EQ_10 ->
                          coe MAlonzo.Code.Haskell.Law.Equality.C_ofN_130
                        MAlonzo.Code.Haskell.Prim.Ord.C_GT_12 ->
                          coe MAlonzo.Code.Haskell.Law.Equality.C_ofY_126 erased
                        _ -> MAlonzo.RTE.mazUnreachableError
                  )
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )
