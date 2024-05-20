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
import qualified MAlonzo.Code.Haskell.Prim
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

-- Peras.SmallStep.Experiment.mkResponse
d_mkResponse_6 ::
  () ->
  ( AgdaAny ->
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_Response_38
  ) ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeTransition_18
    AgdaAny ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeTransition_18
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_Response_38
d_mkResponse_6 ~v0 v1 v2 = du_mkResponse_6 v1 v2
du_mkResponse_6 ::
  ( AgdaAny ->
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_Response_38
  ) ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeTransition_18
    AgdaAny ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeTransition_18
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_Response_38
du_mkResponse_6 v0 v1 =
  case coe v1 of
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.C_MkNodeTransition_30 v2 v3 ->
      coe
        MAlonzo.Code.Peras.SmallStep.Experiment.Types.C_MkNodeTransition_30
        (coe v0 v2)
        (coe v3)
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep.Experiment.nodeTransition'
d_nodeTransition''_14 ::
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeState_8 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeTransition_18
    Bool
d_nodeTransition''_14 =
  coe
    MAlonzo.Code.Peras.SmallStep.Experiment.Impl.d_nodeTransition_16

-- Peras.SmallStep.Experiment.nextState
d_nextState_16 ::
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_Signal_32 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeState_8 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeTransition_18
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_Response_38
d_nextState_16 v0 =
  case coe v0 of
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.C_NewChain_34 v1 ->
      coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        ( coe
            du_mkResponse_6
            ( coe
                MAlonzo.Code.Peras.SmallStep.Experiment.Types.C_ChainAdopted_40
            )
        )
        (coe d_nodeTransition''_14 v1)
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.C_ReportPreference_36 ->
      coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        ( coe
            du_mkResponse_6
            ( coe
                MAlonzo.Code.Peras.SmallStep.Experiment.Types.C_ChainReported_42
            )
        )
        ( coe
            MAlonzo.Code.Peras.SmallStep.Experiment.Impl.d_getPreferredChain_24
        )
    _ -> MAlonzo.RTE.mazUnreachableError
