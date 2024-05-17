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

module MAlonzo.Code.Peras.SmallStep.Experiment.Types where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Peras.Block
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

import qualified Peras.SmallStep.Experiment.Types as G

-- Peras.SmallStep.Experiment.Types.NodeState
d_NodeState_8 = ()
type T_NodeState_8 = G.NodeState
pattern C_MkNodeState_14 a0 = G.MkNodeState a0
check_MkNodeState_14 ::
  MAlonzo.Code.Agda.Builtin.List.T_List_10
    ()
    MAlonzo.Code.Peras.Block.T_Block_62 ->
  T_NodeState_8
check_MkNodeState_14 = G.MkNodeState
cover_NodeState_8 :: G.NodeState -> ()
cover_NodeState_8 x =
  case x of
    G.MkNodeState _ -> ()

-- Peras.SmallStep.Experiment.Types.NodeState.preferredChain
d_preferredChain_12 ::
  T_NodeState_8 -> [MAlonzo.Code.Peras.Block.T_Block_62]
d_preferredChain_12 v0 =
  case coe v0 of
    C_MkNodeState_14 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep.Experiment.Types.NodeTransition
d_NodeTransition_18 a0 = ()
type T_NodeTransition_18 a0 = G.NodeTransition a0
pattern C_MkNodeTransition_30 a0 a1 = G.MkNodeTransition a0 a1
check_MkNodeTransition_30 ::
  forall xa. xa -> T_NodeState_8 -> T_NodeTransition_18 xa
check_MkNodeTransition_30 = G.MkNodeTransition
cover_NodeTransition_18 :: G.NodeTransition a1 -> ()
cover_NodeTransition_18 x =
  case x of
    G.MkNodeTransition _ _ -> ()

-- Peras.SmallStep.Experiment.Types.NodeTransition.output
d_output_26 :: T_NodeTransition_18 AgdaAny -> AgdaAny
d_output_26 v0 =
  case coe v0 of
    C_MkNodeTransition_30 v1 v2 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep.Experiment.Types.NodeTransition.final
d_final_28 :: T_NodeTransition_18 AgdaAny -> T_NodeState_8
d_final_28 v0 =
  case coe v0 of
    C_MkNodeTransition_30 v1 v2 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError
