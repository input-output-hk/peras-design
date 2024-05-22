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
import qualified MAlonzo.Code.Haskell.Prim.Bool
import qualified MAlonzo.Code.Haskell.Prim.Foldable
import qualified MAlonzo.Code.Haskell.Prim.Int
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
nextState ::
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_Signal_42 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeState_8 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeTransition_18
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_Response_48
nextState = coe d_nextState_6
d_nextState_6 ::
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_Signal_42 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeState_8 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeTransition_18
    MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_Response_48
d_nextState_6 =
  coe MAlonzo.Code.Peras.SmallStep.Experiment.Impl.d_signalImpl_42

-- Peras.SmallStep.Experiment.propNeverShortens
propNeverShortens ::
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeState_8 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeState_8 ->
  Bool
propNeverShortens = coe d_propNeverShortens_8
d_propNeverShortens_8 ::
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeState_8 ->
  MAlonzo.Code.Peras.SmallStep.Experiment.Types.T_NodeState_8 ->
  Bool
d_propNeverShortens_8 v0 v1 =
  coe
    MAlonzo.Code.Haskell.Prim.Bool.d__'124''124'__10
    ( coe
        MAlonzo.Code.Haskell.Prim.Int.d_ltInt_66
        ( coe
            MAlonzo.Code.Haskell.Prim.Foldable.du_length_214
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
            ( MAlonzo.Code.Peras.SmallStep.Experiment.Types.d_preferredChain_12
                (coe v0)
            )
        )
        ( coe
            MAlonzo.Code.Haskell.Prim.Foldable.du_length_214
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
            ( MAlonzo.Code.Peras.SmallStep.Experiment.Types.d_preferredChain_12
                (coe v1)
            )
        )
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.Int.d_eqInt_40
        ( coe
            MAlonzo.Code.Haskell.Prim.Foldable.du_length_214
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
            ( MAlonzo.Code.Peras.SmallStep.Experiment.Types.d_preferredChain_12
                (coe v0)
            )
        )
        ( coe
            MAlonzo.Code.Haskell.Prim.Foldable.du_length_214
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
            ( MAlonzo.Code.Peras.SmallStep.Experiment.Types.d_preferredChain_12
                (coe v1)
            )
        )
    )
