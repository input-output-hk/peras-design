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

module MAlonzo.Code.Peras.QQCD.Protocol where

import qualified Data.Text
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

-- Peras.QCD.Protocol.ParamSymbol
d_ParamSymbol_6 = ()
data T_ParamSymbol_6
  = C_U_8
  | C_A_10
  | C_W_12
  | C_L_14
  | C_B_16
  | C_Τ_18
  | C_R_20
  | C_K_22

-- Peras.QCD.Protocol.τ
d_τ_24 :: T_ParamSymbol_6
d_τ_24 = coe C_Τ_18

-- Peras.QCD.Protocol.Params
d_Params_26 = ()
data T_Params_26
  = C_Params'46'constructor_233
      Integer
      Integer
      Integer
      Integer
      Integer
      Integer
      Integer
      Integer

-- Peras.QCD.Protocol.Params.paramU
d_paramU_44 :: T_Params_26 -> Integer
d_paramU_44 v0 =
  case coe v0 of
    C_Params'46'constructor_233 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Protocol.Params.paramA
d_paramA_46 :: T_Params_26 -> Integer
d_paramA_46 v0 =
  case coe v0 of
    C_Params'46'constructor_233 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Protocol.Params.paramW
d_paramW_48 :: T_Params_26 -> Integer
d_paramW_48 v0 =
  case coe v0 of
    C_Params'46'constructor_233 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Protocol.Params.paramL
d_paramL_50 :: T_Params_26 -> Integer
d_paramL_50 v0 =
  case coe v0 of
    C_Params'46'constructor_233 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v4
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Protocol.Params.paramB
d_paramB_52 :: T_Params_26 -> Integer
d_paramB_52 v0 =
  case coe v0 of
    C_Params'46'constructor_233 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v5
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Protocol.Params.paramΤ
d_paramΤ_54 :: T_Params_26 -> Integer
d_paramΤ_54 v0 =
  case coe v0 of
    C_Params'46'constructor_233 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v6
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Protocol.Params.paramR
d_paramR_56 :: T_Params_26 -> Integer
d_paramR_56 v0 =
  case coe v0 of
    C_Params'46'constructor_233 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v7
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Protocol.Params.paramK
d_paramK_58 :: T_Params_26 -> Integer
d_paramK_58 v0 =
  case coe v0 of
    C_Params'46'constructor_233 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v8
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Protocol.defaultParams
d_defaultParams_60 :: T_Params_26
d_defaultParams_60 =
  coe
    C_Params'46'constructor_233
    (coe (120 :: Integer))
    (coe (240 :: Integer))
    (coe (3600 :: Integer))
    (coe (120 :: Integer))
    (coe (10 :: Integer))
    (coe (300 :: Integer))
    (coe (120 :: Integer))
    (coe (600 :: Integer))

-- Peras.QCD.Protocol.perasParam
d_perasParam_62 :: T_ParamSymbol_6 -> T_Params_26 -> Integer
d_perasParam_62 v0 =
  case coe v0 of
    C_U_8 -> coe (\v1 -> d_paramU_44 (coe v1))
    C_A_10 -> coe (\v1 -> d_paramA_46 (coe v1))
    C_W_12 -> coe (\v1 -> d_paramW_48 (coe v1))
    C_L_14 -> coe (\v1 -> d_paramL_50 (coe v1))
    C_B_16 -> coe (\v1 -> d_paramB_52 (coe v1))
    C_Τ_18 -> coe (\v1 -> d_paramΤ_54 (coe v1))
    C_R_20 -> coe (\v1 -> d_paramR_56 (coe v1))
    C_K_22 -> coe (\v1 -> d_paramK_58 (coe v1))
    _ -> MAlonzo.RTE.mazUnreachableError
