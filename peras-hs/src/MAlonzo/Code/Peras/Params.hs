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

module MAlonzo.Code.Peras.Params where

import qualified Data.Text
import qualified MAlonzo.Code.Data.Nat.Base
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

-- Peras.Params.Params
d_Params_4 = ()
data T_Params_4
  = C_Params'46'constructor_77
      Integer
      Integer
      Integer
      Integer
      Integer
      Integer
      Integer
      Integer
      MAlonzo.Code.Data.Nat.Base.T_NonZero_112

-- Peras.Params.Params.T
d_T_24 :: T_Params_4 -> Integer
d_T_24 v0 =
  case coe v0 of
    C_Params'46'constructor_77 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Params.Params.K
d_K_26 :: T_Params_4 -> Integer
d_K_26 v0 =
  case coe v0 of
    C_Params'46'constructor_77 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Params.Params.R
d_R_28 :: T_Params_4 -> Integer
d_R_28 v0 =
  case coe v0 of
    C_Params'46'constructor_77 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Params.Params.L
d_L_30 :: T_Params_4 -> Integer
d_L_30 v0 =
  case coe v0 of
    C_Params'46'constructor_77 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v4
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Params.Params.A
d_A_32 :: T_Params_4 -> Integer
d_A_32 v0 =
  case coe v0 of
    C_Params'46'constructor_77 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v5
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Params.Params.τ
d_τ_34 :: T_Params_4 -> Integer
d_τ_34 v0 =
  case coe v0 of
    C_Params'46'constructor_77 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v6
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Params.Params.B
d_B_36 :: T_Params_4 -> Integer
d_B_36 v0 =
  case coe v0 of
    C_Params'46'constructor_77 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v7
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Params.Params.W
d_W_38 :: T_Params_4 -> Integer
d_W_38 v0 =
  case coe v0 of
    C_Params'46'constructor_77 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v8
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Params.Params.T-nonZero
d_T'45'nonZero_40 ::
  T_Params_4 -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_T'45'nonZero_40 v0 =
  case coe v0 of
    C_Params'46'constructor_77 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v9
    _ -> MAlonzo.RTE.mazUnreachableError
