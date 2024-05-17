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

module MAlonzo.Code.Peras.SmallStep.Experiment where

import qualified Data.Text
import qualified MAlonzo.Code.Peras.Block
import qualified MAlonzo.Code.Peras.SmallStep.Experiment.Impl
import qualified MAlonzo.Code.Peras.SmallStep.Experiment.Types
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

-- Peras.SmallStep.Experiment.nextState
d_nextState_6 ::
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeState_8 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeTransition_18
    Bool
d_nextState_6 =
  coe
    MAlonzo.Code.Peras.SmallStep.Experiment.Impl.d_nodeTransition_16
