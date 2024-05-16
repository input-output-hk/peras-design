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

module MAlonzo.Code.Peras.QQCD.Node.Preagreement where

import qualified Data.Text
import qualified MAlonzo.Code.Haskell.Prim.List
import qualified MAlonzo.Code.Haskell.Prim.Maybe
import qualified MAlonzo.Code.Haskell.Prim.Ord
import qualified MAlonzo.Code.Peras.QQCD.Node.Model
import qualified MAlonzo.Code.Peras.QQCD.Protocol
import qualified MAlonzo.Code.Peras.QQCD.State
import qualified MAlonzo.Code.Peras.QQCD.Types
import qualified MAlonzo.Code.Peras.QQCD.Util
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

-- Peras.QCD.Node.Preagreement.preagreement
d_preagreement_8 :: MAlonzo.Code.Peras.QQCD.State.T_State_10
d_preagreement_8 =
  coe
    MAlonzo.Code.Peras.QQCD.State.du_bindState_114
    ( coe
        MAlonzo.Code.Peras.QQCD.Node.Model.d_peras_58
        (coe MAlonzo.Code.Peras.QQCD.Protocol.C_L_14)
    )
    ( coe
        ( \v0 ->
            coe
              MAlonzo.Code.Peras.QQCD.State.du_bindState_114
              ( coe
                  MAlonzo.Code.Peras.QQCD.State.du_use_260
                  ( \v1 v2 ->
                      coe MAlonzo.Code.Peras.QQCD.Node.Model.du_currentSlot_68 v2
                  )
              )
              ( coe
                  ( \v1 ->
                      coe
                        MAlonzo.Code.Peras.QQCD.Util.du__'8649'__26
                        ( coe
                            MAlonzo.Code.Peras.QQCD.State.du_fmap'61'__130
                            ( \v2 v3 v4 v5 ->
                                coe MAlonzo.Code.Peras.QQCD.State.du_fmapState_68 v4 v5
                            )
                        )
                        ( coe
                            MAlonzo.Code.Peras.QQCD.Util.du__'8649'__26
                            (coe MAlonzo.Code.Peras.QQCD.State.du_iFunctorState_152)
                            ( coe
                                MAlonzo.Code.Peras.QQCD.State.du_use_260
                                ( \v2 v3 ->
                                    coe MAlonzo.Code.Peras.QQCD.Node.Model.du_preferredChain_80 v3
                                )
                            )
                            ( coe
                                MAlonzo.Code.Haskell.Prim.List.du_dropWhile_114
                                (coe d_newerThan_14 (coe v0) (coe v1))
                            )
                        )
                        (coe d_foundBlock_22)
                  )
              )
        )
    )

-- Peras.QCD.Node.Preagreement._.newerThan
d_newerThan_14 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Peras.QQCD.Types.T_Block_50 ->
  Bool
d_newerThan_14 v0 v1 v2 =
  coe
    MAlonzo.Code.Haskell.Prim.Ord.d__'62'__60
    MAlonzo.Code.Haskell.Prim.Ord.d_iOrdNat_246
    ( addInt
        (coe MAlonzo.Code.Peras.QQCD.Types.d_slot_66 (coe v2))
        (coe v0)
    )
    v1

-- Peras.QCD.Node.Preagreement._.foundBlock
d_foundBlock_22 ::
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50] ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10
d_foundBlock_22 v0 =
  case coe v0 of
    [] -> coe MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16
    (:) v1 v2 -> coe MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 (coe v1)
    _ -> MAlonzo.RTE.mazUnreachableError
