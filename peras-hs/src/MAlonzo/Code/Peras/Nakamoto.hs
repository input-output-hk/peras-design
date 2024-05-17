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

module MAlonzo.Code.Peras.Nakamoto where

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

-- Peras.Nakamoto.ConsensusConfig
d_ConsensusConfig_4 = ()
data T_ConsensusConfig_4
  = C_mkConsensusConfig_18
      Integer
      MAlonzo.RTE.Word64
      MAlonzo.RTE.Word64

-- Peras.Nakamoto.ConsensusConfig.partyId
d_partyId_12 :: T_ConsensusConfig_4 -> Integer
d_partyId_12 v0 =
  case coe v0 of
    C_mkConsensusConfig_18 v1 v2 v3 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Nakamoto.ConsensusConfig.roundLength
d_roundLength_14 :: T_ConsensusConfig_4 -> MAlonzo.RTE.Word64
d_roundLength_14 v0 =
  case coe v0 of
    C_mkConsensusConfig_18 v1 v2 v3 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Nakamoto.ConsensusConfig.cooldownPeriod
d_cooldownPeriod_16 :: T_ConsensusConfig_4 -> MAlonzo.RTE.Word64
d_cooldownPeriod_16 v0 =
  case coe v0 of
    C_mkConsensusConfig_18 v1 v2 v3 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError
