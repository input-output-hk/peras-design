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

module MAlonzo.Code.Peras.SmallStep.Experiment.Impl where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Haskell.Prim
import qualified MAlonzo.Code.Haskell.Prim.Ord
import qualified MAlonzo.Code.Peras.Block
import qualified MAlonzo.Code.Peras.Chain
import qualified MAlonzo.Code.Peras.Crypto
import qualified MAlonzo.Code.Peras.Params
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

-- Peras.SmallStep.Experiment.Impl._.hash
d_hash_10 ::
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Crypto.T_Hash_14 AgdaAny
d_hash_10 v0 = coe MAlonzo.Code.Peras.Crypto.d_hash_40 (coe v0)

-- Peras.SmallStep.Experiment.Impl.iBlockHashable
d_iBlockHashable_12 :: MAlonzo.Code.Peras.Crypto.T_Hashable_34
d_iBlockHashable_12 =
  coe
    MAlonzo.Code.Peras.Crypto.C_Hashable'46'constructor_173
    ( coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        (coe MAlonzo.Code.Peras.Crypto.C_MkHash_22)
        ( coe
            MAlonzo.Code.Haskell.Prim.du__'8728'__28
            (coe (\v0 -> MAlonzo.Code.Peras.Crypto.d_bytesS_74 (coe v0)))
            (coe (\v0 -> MAlonzo.Code.Peras.Block.d_signature_104 (coe v0)))
        )
    )

-- Peras.SmallStep.Experiment.Impl.defaultParams
d_defaultParams_14 :: MAlonzo.Code.Peras.Params.T_Params_4
d_defaultParams_14 =
  coe
    MAlonzo.Code.Peras.Params.C_Params'46'constructor_77
    (coe (20 :: Integer))
    (coe (120 :: Integer))
    (coe (120 :: Integer))
    (coe (120 :: Integer))
    (coe (120 :: Integer))
    (coe (20 :: Integer))
    (coe (1 :: Integer))
    (coe (600 :: Integer))
    ( coe
        MAlonzo.Code.Data.Nat.Base.C_NonZero'46'constructor_3581
        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
    )

-- Peras.SmallStep.Experiment.Impl.nodeTransition
nodeTransition ::
  MAlonzo.Code.Agda.Builtin.List.T_List_10
    ()
    MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeState_8 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeTransition_18
    Bool
nodeTransition = coe d_nodeTransition_16
d_nodeTransition_16 ::
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeState_8 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeTransition_18
    Bool
d_nodeTransition_16 v0 v1 =
  coe
    MAlonzo.Code.Haskell.Prim.du_if_then_else__68
    ( coe
        MAlonzo.Code.Haskell.Prim.Ord.d__'62'__60
        MAlonzo.Code.Haskell.Prim.Ord.d_iOrdNat_246
        ( MAlonzo.Code.Peras.Chain.d_'8741'_'8741'__134
            (coe d_iBlockHashable_12)
            (coe d_defaultParams_14)
            (coe v0)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
        )
        ( MAlonzo.Code.Peras.Chain.d_'8741'_'8741'__134
            (coe d_iBlockHashable_12)
            (coe d_defaultParams_14)
            ( coe
                MAlonzo.Code.Peras.SmallStep.Experiment.Types.d_preferredChain_12
                (coe v1)
            )
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
        )
    )
    ( coe
        ( \v2 ->
            coe
              MAlonzo.Code.Haskell.Prim.du__'36'__48
              ( coe
                  MAlonzo.Code.Peras.SmallStep.Experiment.Types.C_MkNodeTransition_30
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
              )
              ( coe
                  MAlonzo.Code.Peras.SmallStep.Experiment.Types.C_MkNodeState_14
                  (coe v0)
              )
        )
    )
    ( coe
        ( \v2 ->
            coe
              MAlonzo.Code.Peras.SmallStep.Experiment.Types.C_MkNodeTransition_30
              (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
              (coe v1)
        )
    )

-- Peras.SmallStep.Experiment.Impl.getPreferredChain
getPreferredChain ::
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeState_8 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeTransition_18
    ( MAlonzo.Code.Agda.Builtin.List.T_List_10
        ()
        MAlonzo.Code.Peras.Block.T_Block_62
    )
getPreferredChain = coe d_getPreferredChain_24
d_getPreferredChain_24 ::
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeState_8 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeTransition_18
    [MAlonzo.Code.Peras.Block.T_Block_62]
d_getPreferredChain_24 v0 =
  coe
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.C_MkNodeTransition_30
    ( coe
        MAlonzo.Code.Peras.SmallStep.Experiment.Types.d_preferredChain_12
        (coe v0)
    )
    (coe v0)
