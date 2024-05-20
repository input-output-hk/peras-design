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
import qualified MAlonzo.Code.Haskell.Prim.Foldable
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

-- Peras.SmallStep.Experiment.Impl.newChain
d_newChain_16 ::
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeState_8 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeTransition_18
    Bool
d_newChain_16 v0 v1 =
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

-- Peras.SmallStep.Experiment.Impl.getChain
d_getChain_24 ::
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeState_8 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeTransition_18
    [MAlonzo.Code.Peras.Block.T_Block_62]
d_getChain_24 v0 =
  coe
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.C_MkNodeTransition_30
    ( coe
        MAlonzo.Code.Peras.SmallStep.Experiment.Types.d_preferredChain_12
        (coe v0)
    )
    (coe v0)

-- Peras.SmallStep.Experiment.Impl.mkResponse
d_mkResponse_28 ::
  () ->
  ( AgdaAny ->
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_Response_48
  ) ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeTransition_18
    AgdaAny ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeTransition_18
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_Response_48
d_mkResponse_28 ~v0 v1 v2 = du_mkResponse_28 v1 v2
du_mkResponse_28 ::
  ( AgdaAny ->
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_Response_48
  ) ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeTransition_18
    AgdaAny ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeTransition_18
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_Response_48
du_mkResponse_28 v0 v1 =
  case coe v1 of
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.C_MkNodeTransition_30 v2 v3 ->
      coe
        MAlonzo.Code.Peras.SmallStep.Experiment.Types.C_MkNodeTransition_30
        (coe v0 v2)
        (coe v3)
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep.Experiment.Impl.transitionImpl
d_transitionImpl_36 ::
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_Act_32 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeState_8 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeTransition_18
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_Response_48
d_transitionImpl_36 v0 =
  case coe v0 of
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.C_NewChain_34 v1 ->
      coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        ( coe
            du_mkResponse_28
            ( coe
                MAlonzo.Code.Peras.SmallStep.Experiment.Types.C_BoolResponse_52
            )
        )
        (coe d_newChain_16 (coe v1))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep.Experiment.Impl.observeImpl
d_observeImpl_40 ::
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_Query_36 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeState_8 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_Response_48
d_observeImpl_40 v0 =
  case coe v0 of
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.C_QueryChain_38 ->
      coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        ( coe
            MAlonzo.Code.Peras.SmallStep.Experiment.Types.C_ChainResponse_56
        )
        ( coe
            ( \v1 ->
                MAlonzo.Code.Peras.SmallStep.Experiment.Types.d_preferredChain_12
                  (coe v1)
            )
        )
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.C_QueryWeight_40 ->
      coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        ( coe
            MAlonzo.Code.Peras.SmallStep.Experiment.Types.C_NatResponse_54
        )
        ( coe
            MAlonzo.Code.Haskell.Prim.du__'8728'__28
            ( coe
                MAlonzo.Code.Haskell.Prim.Foldable.du_foldr_162
                ( coe
                    MAlonzo.Code.Haskell.Prim.Foldable.C_DefaultFoldable'46'constructor_4805
                    ( \v1 v2 v3 v4 v5 ->
                        coe
                          MAlonzo.Code.Haskell.Prim.Foldable.du_foldMapList_408
                          v3
                          v4
                          v5
                    )
                )
                ( coe
                    MAlonzo.Code.Haskell.Prim.du__'36'__48
                    (coe (\v1 v2 -> v1))
                    (coe (\v1 -> addInt (coe (1 :: Integer)) (coe v1)))
                )
                (coe (0 :: Integer))
            )
            ( coe
                ( \v1 ->
                    MAlonzo.Code.Peras.SmallStep.Experiment.Types.d_preferredChain_12
                      (coe v1)
                )
            )
        )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep.Experiment.Impl.signalImpl
signalImpl ::
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_Signal_42 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeState_8 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeTransition_18
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_Response_48
signalImpl = coe d_signalImpl_42
d_signalImpl_42 ::
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_Signal_42 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeState_8 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeTransition_18
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_Response_48
d_signalImpl_42 v0 v1 =
  case coe v0 of
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.C_Transition_44 v2 ->
      coe d_transitionImpl_36 v2 v1
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.C_Observe_46 v2 ->
      coe
        MAlonzo.Code.Peras.SmallStep.Experiment.Types.C_MkNodeTransition_30
        (coe d_observeImpl_40 v2 v1)
        (coe v1)
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep.Experiment.Impl.neverShortens?
neverShortensDec ::
  MAlonzo.Code.Agda.Builtin.List.T_List_10
    ()
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_Act_32 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeState_8 ->
  Bool
neverShortensDec = coe d_neverShortens'63'_52
d_neverShortens'63'_52 ::
  [MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_Act_32] ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeState_8 ->
  Bool
d_neverShortens'63'_52 v0 v1 =
  coe
    MAlonzo.Code.Haskell.Prim.Ord.d__'62''61'__62
    MAlonzo.Code.Haskell.Prim.Ord.d_iOrdNat_246
    ( MAlonzo.Code.Peras.Chain.d_'8741'_'8741'__134
        (coe d_iBlockHashable_12)
        (coe d_defaultParams_14)
        ( coe
            MAlonzo.Code.Peras.SmallStep.Experiment.Types.d_preferredChain_12
            ( coe
                MAlonzo.Code.Haskell.Prim.Foldable.du_foldl_170
                ( coe
                    MAlonzo.Code.Haskell.Prim.Foldable.C_DefaultFoldable'46'constructor_4805
                    ( \v2 v3 v4 v5 v6 ->
                        coe
                          MAlonzo.Code.Haskell.Prim.Foldable.du_foldMapList_408
                          v4
                          v5
                          v6
                    )
                )
                ( coe
                    MAlonzo.Code.Haskell.Prim.du__'36'__48
                    (coe MAlonzo.Code.Haskell.Prim.du_flip_36)
                    ( coe
                        MAlonzo.Code.Haskell.Prim.du__'8728'__28
                        ( coe
                            MAlonzo.Code.Haskell.Prim.du__'8728'__28
                            ( coe
                                ( \v2 ->
                                    MAlonzo.Code.Peras.SmallStep.Experiment.Types.d_final_28
                                      (coe v2)
                                )
                            )
                        )
                        (coe d_transitionImpl_36)
                    )
                )
                (coe v1)
                (coe v0)
            )
        )
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
