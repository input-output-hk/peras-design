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

module MAlonzo.Code.Haskell.Law.Ord.Bool where

import qualified Data.Text
import qualified MAlonzo.Code.Haskell.Law.Eq.Bool
import qualified MAlonzo.Code.Haskell.Law.Ord.Def
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

-- Haskell.Law.Ord.Bool.iLawfulOrdBool
d_iLawfulOrdBool_8 ::
  MAlonzo.Code.Haskell.Law.Ord.Def.T_IsLawfulOrd_12
d_iLawfulOrdBool_8 =
  coe
    MAlonzo.Code.Haskell.Law.Ord.Def.C_IsLawfulOrd'46'constructor_7911
    MAlonzo.Code.Haskell.Law.Eq.Bool.d_iLawfulEqBool_8
