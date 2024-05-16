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

module MAlonzo.Code.Haskell.Law.Eq.Bool where

import qualified Data.Text
import qualified MAlonzo.Code.Haskell.Law.Eq.Def
import qualified MAlonzo.Code.Haskell.Law.Equality
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

-- Haskell.Law.Eq.Bool.iLawfulEqBool
d_iLawfulEqBool_8 ::
  MAlonzo.Code.Haskell.Law.Eq.Def.T_IsLawfulEq_12
d_iLawfulEqBool_8 =
  coe
    MAlonzo.Code.Haskell.Law.Eq.Def.C_IsLawfulEq'46'constructor_169
    ( coe
        ( \v0 ->
            if coe v0
              then
                coe
                  ( \v1 ->
                      if coe v1
                        then coe MAlonzo.Code.Haskell.Law.Equality.C_ofY_126 erased
                        else coe MAlonzo.Code.Haskell.Law.Equality.C_ofN_130
                  )
              else
                coe
                  ( \v1 ->
                      if coe v1
                        then coe MAlonzo.Code.Haskell.Law.Equality.C_ofN_130
                        else coe MAlonzo.Code.Haskell.Law.Equality.C_ofY_126 erased
                  )
        )
    )
