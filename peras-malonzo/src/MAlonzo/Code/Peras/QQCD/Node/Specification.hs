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

module MAlonzo.Code.Peras.QQCD.Node.Specification where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Haskell.Prim
import qualified MAlonzo.Code.Haskell.Prim.Bool
import qualified MAlonzo.Code.Haskell.Prim.Eq
import qualified MAlonzo.Code.Haskell.Prim.Foldable
import qualified MAlonzo.Code.Haskell.Prim.Functor
import qualified MAlonzo.Code.Haskell.Prim.List
import qualified MAlonzo.Code.Haskell.Prim.Maybe
import qualified MAlonzo.Code.Haskell.Prim.Monoid
import qualified MAlonzo.Code.Haskell.Prim.Num
import qualified MAlonzo.Code.Haskell.Prim.Ord
import qualified MAlonzo.Code.Haskell.Prim.Tuple
import qualified MAlonzo.Code.Peras.QQCD.Crypto
import qualified MAlonzo.Code.Peras.QQCD.Crypto.Placeholders
import qualified MAlonzo.Code.Peras.QQCD.Node.Model
import qualified MAlonzo.Code.Peras.QQCD.Node.Preagreement
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

-- Peras.QCD.Node.Specification.initialize
d_initialize_8 ::
  MAlonzo.Code.Peras.QQCD.Protocol.T_Params_26 ->
  MAlonzo.Code.Peras.QQCD.Types.T_VerificationKey_30 ->
  MAlonzo.Code.Peras.QQCD.State.T_State_10
d_initialize_8 v0 v1 =
  coe
    MAlonzo.Code.Peras.QQCD.State.du_bindState_114
    ( coe
        MAlonzo.Code.Peras.QQCD.State.du__'8788'__316
        ( \v2 v3 ->
            coe MAlonzo.Code.Peras.QQCD.Node.Model.du_protocol_52 v3
        )
        v0
    )
    ( coe
        ( \v2 ->
            coe
              MAlonzo.Code.Peras.QQCD.State.du_bindState_114
              ( coe
                  MAlonzo.Code.Peras.QQCD.State.du__'8788'__316
                  ( \v3 v4 ->
                      coe MAlonzo.Code.Peras.QQCD.Node.Model.du_creatorId_62 v4
                  )
                  v1
              )
              (coe (\v3 -> MAlonzo.Code.Peras.QQCD.Node.Model.d_diffuse_124))
        )
    )

-- Peras.QCD.Node.Specification.chainTip
d_chainTip_14 ::
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50] ->
  MAlonzo.Code.Peras.QQCD.Crypto.T_Hash_16
d_chainTip_14 v0 =
  case coe v0 of
    [] -> coe MAlonzo.Code.Peras.QQCD.Types.d_genesisHash_96
    (:) v1 v2 ->
      coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        (coe MAlonzo.Code.Peras.QQCD.Crypto.du_castHash_108)
        ( coe
            MAlonzo.Code.Haskell.Prim.du__'8728'__28
            ( coe
                MAlonzo.Code.Haskell.Prim.du__'8728'__28
                (coe MAlonzo.Code.Peras.QQCD.Crypto.du_castHash_108)
                ( coe
                    MAlonzo.Code.Haskell.Prim.du__'8728'__28
                    ( coe
                        MAlonzo.Code.Haskell.Prim.du__'8728'__28
                        (coe MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24)
                        (coe MAlonzo.Code.Peras.QQCD.Crypto.d_primHashBytes_46)
                    )
                    ( coe
                        ( \v3 ->
                            MAlonzo.Code.Peras.QQCD.Types.d_signatureBytes_26 (coe v3)
                        )
                    )
                )
            )
            ( coe
                (\v3 -> MAlonzo.Code.Peras.QQCD.Types.d_signature_76 (coe v3))
            )
        )
        (coe v1)
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Node.Specification.extendChain
d_extendChain_18 ::
  MAlonzo.Code.Peras.QQCD.Types.T_Block_50 ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50]
d_extendChain_18 = coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22

-- Peras.QCD.Node.Specification.isChainPrefix
d_isChainPrefix_20 ::
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50] ->
  Bool
d_isChainPrefix_20 v0 v1 =
  case coe v0 of
    [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
    (:) v2 v3 -> coe du_test_34 (coe v2) (coe v1)
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Node.Specification._.sl
d_sl_30 ::
  MAlonzo.Code.Peras.QQCD.Types.T_Block_50 ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50] ->
  Integer
d_sl_30 v0 ~v1 ~v2 = du_sl_30 v0
du_sl_30 :: MAlonzo.Code.Peras.QQCD.Types.T_Block_50 -> Integer
du_sl_30 v0 = coe MAlonzo.Code.Peras.QQCD.Types.d_slot_66 (coe v0)

-- Peras.QCD.Node.Specification._.hb
d_hb_32 ::
  MAlonzo.Code.Peras.QQCD.Types.T_Block_50 ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50] ->
  MAlonzo.Code.Peras.QQCD.Crypto.T_Hash_16
d_hb_32 v0 ~v1 ~v2 = du_hb_32 v0
du_hb_32 ::
  MAlonzo.Code.Peras.QQCD.Types.T_Block_50 ->
  MAlonzo.Code.Peras.QQCD.Crypto.T_Hash_16
du_hb_32 v0 =
  coe
    MAlonzo.Code.Haskell.Prim.du__'8728'__28
    (coe MAlonzo.Code.Peras.QQCD.Crypto.du_castHash_108)
    ( coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        ( coe
            MAlonzo.Code.Haskell.Prim.du__'8728'__28
            (coe MAlonzo.Code.Peras.QQCD.Crypto.du_castHash_108)
            ( coe
                MAlonzo.Code.Haskell.Prim.du__'8728'__28
                ( coe
                    MAlonzo.Code.Haskell.Prim.du__'8728'__28
                    (coe MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24)
                    (coe MAlonzo.Code.Peras.QQCD.Crypto.d_primHashBytes_46)
                )
                ( coe
                    ( \v1 ->
                        MAlonzo.Code.Peras.QQCD.Types.d_signatureBytes_26 (coe v1)
                    )
                )
            )
        )
        ( coe
            (\v1 -> MAlonzo.Code.Peras.QQCD.Types.d_signature_76 (coe v1))
        )
    )
    (coe v0)

-- Peras.QCD.Node.Specification._.test
d_test_34 ::
  MAlonzo.Code.Peras.QQCD.Types.T_Block_50 ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50] ->
  Bool
d_test_34 v0 ~v1 ~v2 v3 = du_test_34 v0 v3
du_test_34 ::
  MAlonzo.Code.Peras.QQCD.Types.T_Block_50 ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50] ->
  Bool
du_test_34 v0 v1 =
  case coe v1 of
    [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
    (:) v2 v3 ->
      coe
        MAlonzo.Code.Haskell.Prim.Bool.d__'124''124'__10
        ( coe
            MAlonzo.Code.Peras.QQCD.Crypto.d_eqBS_12
            ( MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
                (coe du_hb_32 (coe v0))
            )
            ( MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
                (coe MAlonzo.Code.Peras.QQCD.Types.d_parent_70 (coe v2))
            )
        )
        ( coe
            MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
            ( coe
                MAlonzo.Code.Haskell.Prim.Ord.d__'60'__58
                MAlonzo.Code.Haskell.Prim.Ord.d_iOrdNat_246
                (coe du_sl_30 (coe v0))
                (MAlonzo.Code.Peras.QQCD.Types.d_slot_66 (coe v2))
            )
            (coe du_test_34 (coe v0) (coe v3))
        )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Node.Specification.updateChains
d_updateChains_44 ::
  [[MAlonzo.Code.Peras.QQCD.Types.T_Block_50]] ->
  MAlonzo.Code.Peras.QQCD.State.T_State_10
d_updateChains_44 v0 =
  coe
    MAlonzo.Code.Peras.QQCD.State.du_bindState_114
    ( coe
        MAlonzo.Code.Peras.QQCD.State.du__'8789'__332
        (\v1 v2 -> coe MAlonzo.Code.Peras.QQCD.Node.Model.du_certs_98 v2)
        ( coe
            du_insertCerts_52
            ( coe
                MAlonzo.Code.Haskell.Prim.Foldable.du_concatMap_190
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
                MAlonzo.Code.Peras.QQCD.Types.d_certsOnChain_114
                v0
            )
        )
    )
    ( coe
        ( \v1 ->
            coe
              MAlonzo.Code.Peras.QQCD.State.du_bindState_114
              ( coe
                  MAlonzo.Code.Peras.QQCD.State.du__'8789'__332
                  (\v2 v3 -> coe MAlonzo.Code.Peras.QQCD.Node.Model.du_chains_86 v3)
                  ( coe
                      MAlonzo.Code.Haskell.Prim.List.du_filter_30
                      ( coe
                          MAlonzo.Code.Haskell.Prim.du__'8728'__28
                          (coe MAlonzo.Code.Haskell.Prim.Bool.d_not_14)
                          (coe du_isPrefixOfAnyChain_54 (coe v0))
                      )
                  )
              )
              ( coe
                  ( \v2 ->
                      coe
                        MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                        ( coe
                            MAlonzo.Code.Peras.QQCD.Util.du__'8649'__26
                            (coe MAlonzo.Code.Peras.QQCD.State.du_iFunctorState_152)
                            ( coe
                                MAlonzo.Code.Peras.QQCD.State.du_use_260
                                ( \v3 v4 ->
                                    coe MAlonzo.Code.Peras.QQCD.Node.Model.du_chains_86 v4
                                )
                            )
                            (coe du_isPrefixOfAnyChain_54)
                        )
                        ( coe
                            ( \v3 ->
                                coe
                                  MAlonzo.Code.Peras.QQCD.State.du__'8789'__332
                                  (\v4 v5 -> coe MAlonzo.Code.Peras.QQCD.Node.Model.du_chains_86 v5)
                                  ( coe
                                      MAlonzo.Code.Haskell.Prim.Monoid.d_mappend_90
                                      (coe MAlonzo.Code.Haskell.Prim.Monoid.du_iMonoidList_158)
                                      ( coe
                                          MAlonzo.Code.Haskell.Prim.List.du_filter_30
                                          ( coe
                                              MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                              (coe MAlonzo.Code.Haskell.Prim.Bool.d_not_14)
                                              (coe v3)
                                          )
                                          (coe v0)
                                      )
                                  )
                            )
                        )
                  )
              )
        )
    )

-- Peras.QCD.Node.Specification._.insertCerts
d_insertCerts_52 ::
  [[MAlonzo.Code.Peras.QQCD.Types.T_Block_50]] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46]
d_insertCerts_52 ~v0 = du_insertCerts_52
du_insertCerts_52 ::
  [MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46]
du_insertCerts_52 =
  coe
    MAlonzo.Code.Peras.QQCD.Util.du_unionDescending_62
    (coe MAlonzo.Code.Haskell.Prim.Ord.d_iOrdNat_246)
    ( coe
        ( \v0 ->
            MAlonzo.Code.Peras.QQCD.Types.d_certificateRound_104 (coe v0)
        )
    )

-- Peras.QCD.Node.Specification._.isPrefixOfAnyChain
d_isPrefixOfAnyChain_54 ::
  [[MAlonzo.Code.Peras.QQCD.Types.T_Block_50]] ->
  [[MAlonzo.Code.Peras.QQCD.Types.T_Block_50]] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50] ->
  Bool
d_isPrefixOfAnyChain_54 ~v0 v1 v2 = du_isPrefixOfAnyChain_54 v1 v2
du_isPrefixOfAnyChain_54 ::
  [[MAlonzo.Code.Peras.QQCD.Types.T_Block_50]] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50] ->
  Bool
du_isPrefixOfAnyChain_54 v0 v1 =
  coe
    MAlonzo.Code.Haskell.Prim.Foldable.du_any_178
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
    (d_isChainPrefix_20 (coe v1))
    v0

-- Peras.QCD.Node.Specification.chainWeight
d_chainWeight_62 ::
  Integer ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50] ->
  Integer
d_chainWeight_62 v0 ~v1 ~v2 = du_chainWeight_62 v0
du_chainWeight_62 :: Integer -> Integer
du_chainWeight_62 v0 =
  coe
    addInt
    (coe MAlonzo.Code.Peras.QQCD.Util.du_count_86)
    ( coe
        mulInt
        (coe v0)
        (coe MAlonzo.Code.Peras.QQCD.Util.du_count_86)
    )

-- Peras.QCD.Node.Specification.heaviestChain
d_heaviestChain_76 ::
  Integer ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46] ->
  [[MAlonzo.Code.Peras.QQCD.Types.T_Block_50]] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50]
d_heaviestChain_76 v0 ~v1 v2 = du_heaviestChain_76 v0 v2
du_heaviestChain_76 ::
  Integer ->
  [[MAlonzo.Code.Peras.QQCD.Types.T_Block_50]] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50]
du_heaviestChain_76 v0 v1 =
  case coe v1 of
    [] -> coe v1
    (:) v2 v3 ->
      coe
        du_heaviest_90
        (coe v0)
        ( coe
            MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24
            (coe v2)
            (coe du_chainWeight_62 (coe v0))
        )
        (coe v3)
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Node.Specification._.heaviest
d_heaviest_90 ::
  Integer ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50] ->
  [[MAlonzo.Code.Peras.QQCD.Types.T_Block_50]] ->
  MAlonzo.Code.Haskell.Prim.Tuple.T__'215'__10 ->
  [[MAlonzo.Code.Peras.QQCD.Types.T_Block_50]] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50]
d_heaviest_90 v0 ~v1 ~v2 ~v3 v4 v5 = du_heaviest_90 v0 v4 v5
du_heaviest_90 ::
  Integer ->
  MAlonzo.Code.Haskell.Prim.Tuple.T__'215'__10 ->
  [[MAlonzo.Code.Peras.QQCD.Types.T_Block_50]] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50]
du_heaviest_90 v0 v1 v2 =
  case coe v1 of
    MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24 v3 v4 ->
      case coe v2 of
        [] -> coe v3
        (:) v5 v6 ->
          coe
            MAlonzo.Code.Haskell.Prim.du_if_then_else__68
            ( coe
                MAlonzo.Code.Haskell.Prim.Ord.d__'60''61'__64
                MAlonzo.Code.Haskell.Prim.Ord.d_iOrdNat_246
                v4
                (coe du_chainWeight_62 (coe v0))
            )
            ( coe
                ( \v7 ->
                    coe
                      du_heaviest_90
                      (coe v0)
                      ( coe
                          MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24
                          (coe v5)
                          (coe du_chainWeight_62 (coe v0))
                      )
                      (coe v6)
                )
            )
            (coe (\v7 -> coe du_heaviest_90 (coe v0) (coe v1) (coe v6)))
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Node.Specification.certificatesForNewQuorums
d_certificatesForNewQuorums_104 ::
  MAlonzo.Code.Peras.QQCD.State.T_State_10
d_certificatesForNewQuorums_104 =
  coe
    MAlonzo.Code.Peras.QQCD.State.du_bindState_114
    ( coe
        MAlonzo.Code.Peras.QQCD.Node.Model.d_peras_58
        (coe MAlonzo.Code.Peras.QQCD.Protocol.d_τ_24)
    )
    ( coe
        ( \v0 ->
            coe
              MAlonzo.Code.Peras.QQCD.State.du_bindState_114
              ( coe
                  MAlonzo.Code.Peras.QQCD.Util.du__'8649'__26
                  (coe MAlonzo.Code.Peras.QQCD.State.du_iFunctorState_152)
                  ( coe
                      MAlonzo.Code.Peras.QQCD.State.du_use_260
                      (\v1 v2 -> coe MAlonzo.Code.Peras.QQCD.Node.Model.du_certs_98 v2)
                  )
                  ( coe
                      MAlonzo.Code.Haskell.Prim.List.du_map_6
                      ( coe
                          ( \v1 ->
                              MAlonzo.Code.Peras.QQCD.Types.d_certificateRound_104 (coe v1)
                          )
                      )
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
                            ( coe
                                MAlonzo.Code.Peras.QQCD.State.du_fmap'61'__130
                                ( \v2 v3 v4 v5 ->
                                    coe MAlonzo.Code.Peras.QQCD.State.du_fmapState_68 v4 v5
                                )
                            )
                            ( coe
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
                                            coe MAlonzo.Code.Peras.QQCD.Node.Model.du_votes_92 v3
                                        )
                                    )
                                    ( coe
                                        MAlonzo.Code.Haskell.Prim.List.du_filter_30
                                        (coe d_hasNoCertificate_110 (coe v1))
                                    )
                                )
                                (coe d_groupByRound_116)
                            )
                            ( coe
                                MAlonzo.Code.Haskell.Prim.List.du_filter_30
                                (coe d_hasQuorum_118 (coe v0))
                            )
                        )
                        ( coe
                            MAlonzo.Code.Haskell.Prim.List.du_map_6
                            ( coe
                                MAlonzo.Code.Peras.QQCD.Crypto.Placeholders.d_buildCertificate_36
                            )
                        )
                  )
              )
        )
    )

-- Peras.QCD.Node.Specification._.hasNoCertificate
d_hasNoCertificate_110 ::
  [Integer] -> MAlonzo.Code.Peras.QQCD.Types.T_Vote_126 -> Bool
d_hasNoCertificate_110 v0 v1 =
  coe
    MAlonzo.Code.Haskell.Prim.Foldable.du_notElem_198
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
    (coe MAlonzo.Code.Haskell.Prim.Eq.d_iEqNat_28)
    (coe MAlonzo.Code.Peras.QQCD.Types.d_voteRound_140 (coe v1))
    (coe v0)

-- Peras.QCD.Node.Specification._.groupByRound
d_groupByRound_116 ::
  [MAlonzo.Code.Peras.QQCD.Types.T_Vote_126] ->
  [[MAlonzo.Code.Peras.QQCD.Types.T_Vote_126]]
d_groupByRound_116 =
  coe
    MAlonzo.Code.Peras.QQCD.Util.du_groupBy_74
    ( coe
        MAlonzo.Code.Peras.QQCD.Util.du_eqBy_8
        (coe MAlonzo.Code.Haskell.Prim.Eq.d_iEqNat_28)
        ( coe
            (\v0 -> MAlonzo.Code.Peras.QQCD.Types.d_voteRound_140 (coe v0))
        )
    )

-- Peras.QCD.Node.Specification._.hasQuorum
d_hasQuorum_118 ::
  Integer -> [MAlonzo.Code.Peras.QQCD.Types.T_Vote_126] -> Bool
d_hasQuorum_118 v0 v1 =
  coe
    MAlonzo.Code.Haskell.Prim.Ord.d__'62''61'__62
    MAlonzo.Code.Haskell.Prim.Ord.d_iOrdNat_246
    ( coe
        MAlonzo.Code.Haskell.Prim.Foldable.du_sum_208
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
        MAlonzo.Code.Haskell.Prim.Num.d_iNumNat_104
        ( coe
            MAlonzo.Code.Haskell.Prim.List.du_map_6
            ( coe
                (\v2 -> MAlonzo.Code.Peras.QQCD.Types.d_voteWeight_144 (coe v2))
            )
            (coe v1)
        )
    )
    v0

-- Peras.QCD.Node.Specification.updateLatestCertSeen
d_updateLatestCertSeen_128 ::
  MAlonzo.Code.Peras.QQCD.State.T_State_10
d_updateLatestCertSeen_128 =
  coe
    MAlonzo.Code.Peras.QQCD.State.du_bindState_114
    ( coe
        MAlonzo.Code.Peras.QQCD.Util.du__'8649'__26
        ( coe
            MAlonzo.Code.Peras.QQCD.State.du_fmap'61'__130
            ( \v0 v1 v2 v3 ->
                coe MAlonzo.Code.Peras.QQCD.State.du_fmapState_68 v2 v3
            )
        )
        ( coe
            MAlonzo.Code.Peras.QQCD.State.du_use_260
            (\v0 v1 -> coe MAlonzo.Code.Peras.QQCD.Node.Model.du_certs_98 v1)
        )
        ( coe
            MAlonzo.Code.Peras.QQCD.Util.du_firstWithDefault_88
            (coe MAlonzo.Code.Peras.QQCD.Types.d_genesisCert_112)
        )
    )
    ( coe
        MAlonzo.Code.Peras.QQCD.State.du__'8788'__316
        ( \v0 v1 ->
            coe MAlonzo.Code.Peras.QQCD.Node.Model.du_latestCertSeen_104 v1
        )
    )

-- Peras.QCD.Node.Specification.updateLatestCertOnChain
d_updateLatestCertOnChain_132 ::
  MAlonzo.Code.Peras.QQCD.State.T_State_10
d_updateLatestCertOnChain_132 =
  coe
    MAlonzo.Code.Peras.QQCD.State.du_bindState_114
    ( coe
        MAlonzo.Code.Peras.QQCD.Util.du__'8649'__26
        ( coe
            MAlonzo.Code.Peras.QQCD.State.du_fmap'61'__130
            ( \v0 v1 v2 v3 ->
                coe MAlonzo.Code.Peras.QQCD.State.du_fmapState_68 v2 v3
            )
        )
        ( coe
            MAlonzo.Code.Peras.QQCD.State.du_use_260
            ( \v0 v1 ->
                coe MAlonzo.Code.Peras.QQCD.Node.Model.du_preferredChain_80 v1
            )
        )
        (coe MAlonzo.Code.Peras.QQCD.Types.d_lastCert_120)
    )
    ( coe
        MAlonzo.Code.Peras.QQCD.State.du__'8788'__316
        ( \v0 v1 ->
            coe
              MAlonzo.Code.Peras.QQCD.Node.Model.du_latestCertOnChain_110
              v1
        )
    )

-- Peras.QCD.Node.Specification.fetching
d_fetching_136 ::
  [[MAlonzo.Code.Peras.QQCD.Types.T_Block_50]] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Vote_126] ->
  MAlonzo.Code.Peras.QQCD.State.T_State_10
d_fetching_136 v0 v1 =
  coe
    MAlonzo.Code.Peras.QQCD.State.du_bindState_114
    ( coe
        MAlonzo.Code.Peras.QQCD.State.du__'8789'__332
        ( \v2 v3 ->
            coe MAlonzo.Code.Peras.QQCD.Node.Model.du_currentSlot_68 v3
        )
        MAlonzo.Code.Peras.QQCD.Util.d_addOne_32
    )
    ( coe
        ( \v2 ->
            coe
              MAlonzo.Code.Peras.QQCD.State.du_bindState_114
              ( coe
                  MAlonzo.Code.Peras.QQCD.Node.Model.d_peras_58
                  (coe MAlonzo.Code.Peras.QQCD.Protocol.C_U_8)
              )
              ( coe
                  ( \v3 ->
                      coe
                        MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                        ( coe
                            MAlonzo.Code.Peras.QQCD.State.du_use_260
                            ( \v4 v5 ->
                                coe MAlonzo.Code.Peras.QQCD.Node.Model.du_currentSlot_68 v5
                            )
                        )
                        ( coe
                            ( \v4 ->
                                coe
                                  MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                  ( coe
                                      MAlonzo.Code.Peras.QQCD.State.du__'8788'__316
                                      ( \v5 v6 ->
                                          coe MAlonzo.Code.Peras.QQCD.Node.Model.du_currentRound_74 v6
                                      )
                                      (MAlonzo.Code.Peras.QQCD.Util.d_divideNat_104 (coe v4) (coe v3))
                                  )
                                  ( coe
                                      ( \v5 ->
                                          coe
                                            MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                            (coe d_updateChains_44 (coe v0))
                                            ( coe
                                                ( \v6 ->
                                                    coe
                                                      MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                                      ( coe
                                                          MAlonzo.Code.Peras.QQCD.State.du__'8789'__332
                                                          ( \v7 v8 ->
                                                              coe
                                                                MAlonzo.Code.Peras.QQCD.Node.Model.du_votes_92
                                                                v8
                                                          )
                                                          (coe du_insertVotes_146 v1)
                                                      )
                                                      ( coe
                                                          ( \v7 ->
                                                              coe
                                                                MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                                                (coe d_certificatesForNewQuorums_104)
                                                                ( coe
                                                                    ( \v8 ->
                                                                        coe
                                                                          MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                                                          ( coe
                                                                              MAlonzo.Code.Peras.QQCD.State.du__'8789'__332
                                                                              ( \v9 v10 ->
                                                                                  coe
                                                                                    MAlonzo.Code.Peras.QQCD.Node.Model.du_certs_98
                                                                                    v10
                                                                              )
                                                                              (coe du_insertCerts_148 v8)
                                                                          )
                                                                          ( coe
                                                                              ( \v9 ->
                                                                                  coe
                                                                                    MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                                                                    ( coe
                                                                                        MAlonzo.Code.Peras.QQCD.Node.Model.d_peras_58
                                                                                        ( coe
                                                                                            MAlonzo.Code.Peras.QQCD.Protocol.C_B_16
                                                                                        )
                                                                                    )
                                                                                    ( coe
                                                                                        ( \v10 ->
                                                                                            coe
                                                                                              MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                                                                              ( coe
                                                                                                  MAlonzo.Code.Peras.QQCD.State.du_apState_94
                                                                                                  ( coe
                                                                                                      MAlonzo.Code.Haskell.Prim.Functor.d__'60''36''62'__26
                                                                                                      ( coe
                                                                                                          MAlonzo.Code.Peras.QQCD.State.du_iFunctorState_152
                                                                                                      )
                                                                                                      erased
                                                                                                      erased
                                                                                                      ( \v11 v12 ->
                                                                                                          coe
                                                                                                            du_heaviestChain_76
                                                                                                            (coe v10)
                                                                                                            v12
                                                                                                      )
                                                                                                      ( coe
                                                                                                          MAlonzo.Code.Peras.QQCD.State.du_use_260
                                                                                                          ( \v11 v12 ->
                                                                                                              coe
                                                                                                                MAlonzo.Code.Peras.QQCD.Node.Model.du_certs_98
                                                                                                                v12
                                                                                                          )
                                                                                                      )
                                                                                                  )
                                                                                                  ( coe
                                                                                                      MAlonzo.Code.Peras.QQCD.State.du_use_260
                                                                                                      ( \v11 v12 ->
                                                                                                          coe
                                                                                                            MAlonzo.Code.Peras.QQCD.Node.Model.du_chains_86
                                                                                                            v12
                                                                                                      )
                                                                                                  )
                                                                                              )
                                                                                              ( coe
                                                                                                  ( \v11 ->
                                                                                                      coe
                                                                                                        MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                                                                                        ( coe
                                                                                                            MAlonzo.Code.Peras.QQCD.State.du__'8788'__316
                                                                                                            ( \v12
                                                                                                               v13 ->
                                                                                                                  coe
                                                                                                                    MAlonzo.Code.Peras.QQCD.Node.Model.du_preferredChain_80
                                                                                                                    v13
                                                                                                            )
                                                                                                            v11
                                                                                                        )
                                                                                                        ( coe
                                                                                                            ( \v12 ->
                                                                                                                coe
                                                                                                                  MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                                                                                                  ( coe
                                                                                                                      d_updateLatestCertSeen_128
                                                                                                                  )
                                                                                                                  ( coe
                                                                                                                      ( \v13 ->
                                                                                                                          coe
                                                                                                                            MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                                                                                                            ( coe
                                                                                                                                d_updateLatestCertOnChain_132
                                                                                                                            )
                                                                                                                            ( coe
                                                                                                                                ( \v14 ->
                                                                                                                                    MAlonzo.Code.Peras.QQCD.Node.Model.d_diffuse_124
                                                                                                                                )
                                                                                                                            )
                                                                                                                      )
                                                                                                                  )
                                                                                                            )
                                                                                                        )
                                                                                                  )
                                                                                              )
                                                                                        )
                                                                                    )
                                                                              )
                                                                          )
                                                                    )
                                                                )
                                                          )
                                                      )
                                                )
                                            )
                                      )
                                  )
                            )
                        )
                  )
              )
        )
    )

-- Peras.QCD.Node.Specification._.insertVotes
d_insertVotes_146 ::
  [[MAlonzo.Code.Peras.QQCD.Types.T_Block_50]] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Vote_126] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Vote_126] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Vote_126] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Vote_126]
d_insertVotes_146 ~v0 ~v1 = du_insertVotes_146
du_insertVotes_146 ::
  [MAlonzo.Code.Peras.QQCD.Types.T_Vote_126] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Vote_126] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Vote_126]
du_insertVotes_146 =
  coe
    MAlonzo.Code.Peras.QQCD.Util.du_unionDescending_62
    (coe MAlonzo.Code.Haskell.Prim.Ord.d_iOrdNat_246)
    ( coe
        (\v0 -> MAlonzo.Code.Peras.QQCD.Types.d_voteRound_140 (coe v0))
    )

-- Peras.QCD.Node.Specification._.insertCerts
d_insertCerts_148 ::
  [[MAlonzo.Code.Peras.QQCD.Types.T_Block_50]] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Vote_126] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46]
d_insertCerts_148 ~v0 ~v1 = du_insertCerts_148
du_insertCerts_148 ::
  [MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46]
du_insertCerts_148 =
  coe
    MAlonzo.Code.Peras.QQCD.Util.du_unionDescending_62
    (coe MAlonzo.Code.Haskell.Prim.Ord.d_iOrdNat_246)
    ( coe
        ( \v0 ->
            MAlonzo.Code.Peras.QQCD.Types.d_certificateRound_104 (coe v0)
        )
    )

-- Peras.QCD.Node.Specification.blockCreation
d_blockCreation_160 ::
  [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6] ->
  MAlonzo.Code.Peras.QQCD.State.T_State_10
d_blockCreation_160 v0 =
  coe
    MAlonzo.Code.Peras.QQCD.State.du_bindState_114
    ( coe
        MAlonzo.Code.Peras.QQCD.Util.du__'8649'__26
        ( coe
            MAlonzo.Code.Peras.QQCD.State.du_fmap'61'__130
            ( \v1 v2 v3 v4 ->
                coe MAlonzo.Code.Peras.QQCD.State.du_fmapState_68 v3 v4
            )
        )
        ( coe
            MAlonzo.Code.Peras.QQCD.State.du_use_260
            ( \v1 v2 ->
                coe MAlonzo.Code.Peras.QQCD.Node.Model.du_preferredChain_80 v2
            )
        )
        (coe d_chainTip_14)
    )
    ( coe
        ( \v1 ->
            coe
              MAlonzo.Code.Peras.QQCD.State.du_bindState_114
              ( coe
                  MAlonzo.Code.Peras.QQCD.Node.Model.d_peras_58
                  (coe MAlonzo.Code.Peras.QQCD.Protocol.C_A_10)
              )
              ( coe
                  ( \v2 ->
                      coe
                        MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                        ( coe
                            MAlonzo.Code.Peras.QQCD.State.du_use_260
                            ( \v3 v4 ->
                                coe MAlonzo.Code.Peras.QQCD.Node.Model.du_currentRound_74 v4
                            )
                        )
                        ( coe
                            ( \v3 ->
                                coe
                                  MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                  ( coe
                                      MAlonzo.Code.Peras.QQCD.State.du_use_260
                                      ( \v4 v5 ->
                                          coe
                                            MAlonzo.Code.Peras.QQCD.Node.Model.du_latestCertSeen_104
                                            v5
                                      )
                                  )
                                  ( coe
                                      ( \v4 ->
                                          coe
                                            MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                            ( coe
                                                MAlonzo.Code.Peras.QQCD.State.du_use_260
                                                ( \v5 v6 ->
                                                    coe
                                                      MAlonzo.Code.Peras.QQCD.Node.Model.du_latestCertOnChain_110
                                                      v6
                                                )
                                            )
                                            ( coe
                                                ( \v5 ->
                                                    coe
                                                      MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                                      ( coe
                                                          MAlonzo.Code.Peras.QQCD.Util.du__'8649'__26
                                                          ( coe
                                                              MAlonzo.Code.Peras.QQCD.State.du_iFunctorState_152
                                                          )
                                                          ( coe
                                                              MAlonzo.Code.Peras.QQCD.Util.du__'8649'__26
                                                              ( coe
                                                                  MAlonzo.Code.Peras.QQCD.State.du_iFunctorState_152
                                                              )
                                                              ( coe
                                                                  MAlonzo.Code.Peras.QQCD.State.du_use_260
                                                                  ( \v6 v7 ->
                                                                      coe
                                                                        MAlonzo.Code.Peras.QQCD.Node.Model.du_certs_98
                                                                        v7
                                                                  )
                                                              )
                                                              ( coe
                                                                  MAlonzo.Code.Haskell.Prim.List.du_takeWhile_104
                                                                  ( coe
                                                                      du_noMoreThanTwoRoundsOld_168
                                                                      (coe v3)
                                                                  )
                                                              )
                                                          )
                                                          ( coe
                                                              MAlonzo.Code.Haskell.Prim.Foldable.d_any_54
                                                              MAlonzo.Code.Haskell.Prim.Foldable.d_iFoldableList_402
                                                              erased
                                                              (coe du_twoRoundsOld_174 (coe v3))
                                                          )
                                                      )
                                                      ( coe
                                                          ( \v6 ->
                                                              coe
                                                                MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                                                ( coe
                                                                    MAlonzo.Code.Haskell.Prim.du__'36'__48
                                                                    ( coe
                                                                        ( \v7 ->
                                                                            coe
                                                                              MAlonzo.Code.Peras.QQCD.State.du_pureState_82
                                                                              (coe v7)
                                                                        )
                                                                    )
                                                                    ( coe
                                                                        MAlonzo.Code.Haskell.Prim.Ord.d__'60''61'__64
                                                                        MAlonzo.Code.Haskell.Prim.Ord.d_iOrdNat_246
                                                                        v3
                                                                        ( addInt
                                                                            ( coe
                                                                                MAlonzo.Code.Peras.QQCD.Types.d_certificateRound_104
                                                                                (coe v4)
                                                                            )
                                                                            (coe v2)
                                                                        )
                                                                    )
                                                                )
                                                                ( coe
                                                                    ( \v7 ->
                                                                        coe
                                                                          MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                                                          ( coe
                                                                              MAlonzo.Code.Haskell.Prim.du__'36'__48
                                                                              ( coe
                                                                                  ( \v8 ->
                                                                                      coe
                                                                                        MAlonzo.Code.Peras.QQCD.State.du_pureState_82
                                                                                        (coe v8)
                                                                                  )
                                                                              )
                                                                              ( coe
                                                                                  MAlonzo.Code.Haskell.Prim.Ord.d__'62'__60
                                                                                  MAlonzo.Code.Haskell.Prim.Ord.d_iOrdNat_246
                                                                                  ( MAlonzo.Code.Peras.QQCD.Types.d_certificateRound_104
                                                                                      (coe v4)
                                                                                  )
                                                                                  ( MAlonzo.Code.Peras.QQCD.Types.d_certificateRound_104
                                                                                      (coe v5)
                                                                                  )
                                                                              )
                                                                          )
                                                                          ( coe
                                                                              ( \v8 ->
                                                                                  coe
                                                                                    MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                                                                    ( coe
                                                                                        MAlonzo.Code.Peras.QQCD.State.du_pureState_82
                                                                                        ( coe
                                                                                            MAlonzo.Code.Haskell.Prim.du_if_then_else__68
                                                                                            ( coe
                                                                                                MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                                                                                                ( coe
                                                                                                    MAlonzo.Code.Haskell.Prim.Bool.d_not_14
                                                                                                    (coe v6)
                                                                                                )
                                                                                                ( coe
                                                                                                    MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                                                                                                    (coe v7)
                                                                                                    (coe v8)
                                                                                                )
                                                                                            )
                                                                                            ( coe
                                                                                                ( \v9 ->
                                                                                                    coe
                                                                                                      MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18
                                                                                                      (coe v4)
                                                                                                )
                                                                                            )
                                                                                            ( coe
                                                                                                ( \v9 ->
                                                                                                    coe
                                                                                                      MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16
                                                                                                )
                                                                                            )
                                                                                        )
                                                                                    )
                                                                                    ( coe
                                                                                        ( \v9 ->
                                                                                            coe
                                                                                              MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                                                                              ( coe
                                                                                                  MAlonzo.Code.Peras.QQCD.State.du_apState_94
                                                                                                  ( coe
                                                                                                      MAlonzo.Code.Peras.QQCD.State.du_apState_94
                                                                                                      ( coe
                                                                                                          MAlonzo.Code.Peras.QQCD.State.du_apState_94
                                                                                                          ( coe
                                                                                                              MAlonzo.Code.Peras.QQCD.State.du_apState_94
                                                                                                              ( coe
                                                                                                                  MAlonzo.Code.Haskell.Prim.Functor.d__'60''36''62'__26
                                                                                                                  ( coe
                                                                                                                      MAlonzo.Code.Peras.QQCD.State.du_iFunctorState_152
                                                                                                                  )
                                                                                                                  erased
                                                                                                                  erased
                                                                                                                  MAlonzo.Code.Peras.QQCD.Crypto.Placeholders.d_signBlock_14
                                                                                                                  ( coe
                                                                                                                      MAlonzo.Code.Peras.QQCD.State.du_use_260
                                                                                                                      ( \v10
                                                                                                                         v11 ->
                                                                                                                            coe
                                                                                                                              MAlonzo.Code.Peras.QQCD.Node.Model.du_currentSlot_68
                                                                                                                              v11
                                                                                                                      )
                                                                                                                  )
                                                                                                              )
                                                                                                              ( coe
                                                                                                                  MAlonzo.Code.Peras.QQCD.State.du_use_260
                                                                                                                  ( \v10
                                                                                                                     v11 ->
                                                                                                                        coe
                                                                                                                          MAlonzo.Code.Peras.QQCD.Node.Model.du_creatorId_62
                                                                                                                          v11
                                                                                                                  )
                                                                                                              )
                                                                                                          )
                                                                                                          ( coe
                                                                                                              MAlonzo.Code.Peras.QQCD.State.du_pureState_82
                                                                                                              (coe v1)
                                                                                                          )
                                                                                                      )
                                                                                                      ( coe
                                                                                                          MAlonzo.Code.Peras.QQCD.State.du_pureState_82
                                                                                                          (coe v9)
                                                                                                      )
                                                                                                  )
                                                                                                  ( coe
                                                                                                      MAlonzo.Code.Peras.QQCD.State.du_pureState_82
                                                                                                      (coe v0)
                                                                                                  )
                                                                                              )
                                                                                              ( coe
                                                                                                  ( \v10 ->
                                                                                                      coe
                                                                                                        MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                                                                                        ( coe
                                                                                                            MAlonzo.Code.Peras.QQCD.Util.du__'8649'__26
                                                                                                            ( coe
                                                                                                                MAlonzo.Code.Peras.QQCD.State.du_iFunctorState_152
                                                                                                            )
                                                                                                            ( coe
                                                                                                                MAlonzo.Code.Peras.QQCD.State.du_use_260
                                                                                                                ( \v11
                                                                                                                   v12 ->
                                                                                                                      coe
                                                                                                                        MAlonzo.Code.Peras.QQCD.Node.Model.du_preferredChain_80
                                                                                                                        v12
                                                                                                                )
                                                                                                            )
                                                                                                            ( coe
                                                                                                                d_extendChain_18
                                                                                                                v10
                                                                                                            )
                                                                                                        )
                                                                                                        ( coe
                                                                                                            ( \v11 ->
                                                                                                                coe
                                                                                                                  MAlonzo.Code.Peras.QQCD.Util.du__'8606'__96
                                                                                                                  ( coe
                                                                                                                      MAlonzo.Code.Peras.QQCD.State.du_iApplicativeState_156
                                                                                                                  )
                                                                                                                  ( coe
                                                                                                                      MAlonzo.Code.Peras.QQCD.Node.Model.d_diffuse_124
                                                                                                                  )
                                                                                                                  ( coe
                                                                                                                      MAlonzo.Code.Peras.QQCD.Types.C_NewChain_156
                                                                                                                      ( coe
                                                                                                                          v11
                                                                                                                      )
                                                                                                                  )
                                                                                                            )
                                                                                                        )
                                                                                                  )
                                                                                              )
                                                                                        )
                                                                                    )
                                                                              )
                                                                          )
                                                                    )
                                                                )
                                                          )
                                                      )
                                                )
                                            )
                                      )
                                  )
                            )
                        )
                  )
              )
        )
    )

-- Peras.QCD.Node.Specification._.noMoreThanTwoRoundsOld
d_noMoreThanTwoRoundsOld_168 ::
  [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6] ->
  Integer ->
  MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46 ->
  Bool
d_noMoreThanTwoRoundsOld_168 ~v0 v1 v2 =
  du_noMoreThanTwoRoundsOld_168 v1 v2
du_noMoreThanTwoRoundsOld_168 ::
  Integer -> MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46 -> Bool
du_noMoreThanTwoRoundsOld_168 v0 v1 =
  coe
    MAlonzo.Code.Haskell.Prim.Ord.d__'60''61'__64
    MAlonzo.Code.Haskell.Prim.Ord.d_iOrdNat_246
    ( addInt
        (coe (2 :: Integer))
        ( coe
            MAlonzo.Code.Peras.QQCD.Types.d_certificateRound_104
            (coe v1)
        )
    )
    v0

-- Peras.QCD.Node.Specification._.twoRoundsOld
d_twoRoundsOld_174 ::
  [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6] ->
  Integer ->
  MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46 ->
  Bool
d_twoRoundsOld_174 ~v0 v1 v2 = du_twoRoundsOld_174 v1 v2
du_twoRoundsOld_174 ::
  Integer -> MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46 -> Bool
du_twoRoundsOld_174 v0 v1 =
  coe
    eqInt
    ( coe
        addInt
        (coe (2 :: Integer))
        ( coe
            MAlonzo.Code.Peras.QQCD.Types.d_certificateRound_104
            (coe v1)
        )
    )
    (coe v0)

-- Peras.QCD.Node.Specification.extends
d_extends_202 ::
  MAlonzo.Code.Peras.QQCD.Types.T_Block_50 ->
  MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46 ->
  [[MAlonzo.Code.Peras.QQCD.Types.T_Block_50]] ->
  Bool
d_extends_202 v0 v1 =
  coe
    MAlonzo.Code.Haskell.Prim.Foldable.du_any_178
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
    (d_chainExtends_228 (coe v0) (coe v1))

-- Peras.QCD.Node.Specification._.dropUntilBlock
d_dropUntilBlock_212 ::
  MAlonzo.Code.Peras.QQCD.Types.T_Block_50 ->
  MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46 ->
  Integer ->
  MAlonzo.Code.Peras.QQCD.Crypto.T_Hash_16 ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50]
d_dropUntilBlock_212 ~v0 ~v1 v2 v3 v4 =
  du_dropUntilBlock_212 v2 v3 v4
du_dropUntilBlock_212 ::
  Integer ->
  MAlonzo.Code.Peras.QQCD.Crypto.T_Hash_16 ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50]
du_dropUntilBlock_212 v0 v1 v2 =
  coe
    MAlonzo.Code.Haskell.Prim.du_case_of__58
    ( coe
        MAlonzo.Code.Haskell.Prim.List.du_dropWhile_114
        ( coe
            ( \v3 ->
                coe
                  MAlonzo.Code.Haskell.Prim.Ord.d__'60'__58
                  MAlonzo.Code.Haskell.Prim.Ord.d_iOrdNat_246
                  v0
                  (MAlonzo.Code.Peras.QQCD.Types.d_slot_66 (coe v3))
            )
        )
        (coe v2)
    )
    ( coe
        ( \v3 v4 ->
            case coe v3 of
              [] -> coe v3
              (:) v5 v6 ->
                coe
                  MAlonzo.Code.Haskell.Prim.du_if_then_else__68
                  ( coe
                      MAlonzo.Code.Peras.QQCD.Crypto.d_eqBS_12
                      (MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22 (coe v1))
                      ( MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
                          ( coe
                              MAlonzo.Code.Haskell.Prim.du__'8728'__28
                              (coe MAlonzo.Code.Peras.QQCD.Crypto.du_castHash_108)
                              ( coe
                                  MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                  ( coe
                                      MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                      (coe MAlonzo.Code.Peras.QQCD.Crypto.du_castHash_108)
                                      ( coe
                                          MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                          ( coe
                                              MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                              (coe MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24)
                                              (coe MAlonzo.Code.Peras.QQCD.Crypto.d_primHashBytes_46)
                                          )
                                          ( coe
                                              ( \v7 ->
                                                  MAlonzo.Code.Peras.QQCD.Types.d_signatureBytes_26
                                                    (coe v7)
                                              )
                                          )
                                      )
                                  )
                                  ( coe
                                      ( \v7 ->
                                          MAlonzo.Code.Peras.QQCD.Types.d_signature_76 (coe v7)
                                      )
                                  )
                              )
                              (coe v5)
                          )
                      )
                  )
                  ( coe
                      ( \v7 ->
                          coe
                            MAlonzo.Code.Haskell.Prim.List.du_dropWhile_114
                            ( coe
                                ( \v8 ->
                                    coe
                                      MAlonzo.Code.Haskell.Prim.Ord.d__'60'__58
                                      MAlonzo.Code.Haskell.Prim.Ord.d_iOrdNat_246
                                      v0
                                      (MAlonzo.Code.Peras.QQCD.Types.d_slot_66 (coe v8))
                                )
                            )
                            (coe v2)
                      )
                  )
                  (coe (\v7 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Peras.QCD.Node.Specification._.chainExtends
d_chainExtends_228 ::
  MAlonzo.Code.Peras.QQCD.Types.T_Block_50 ->
  MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46 ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50] ->
  Bool
d_chainExtends_228 v0 v1 =
  coe
    MAlonzo.Code.Haskell.Prim.du__'8728'__28
    ( coe
        MAlonzo.Code.Haskell.Prim.Foldable.du_any_178
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
        ( \v2 ->
            coe
              MAlonzo.Code.Peras.QQCD.Crypto.d_eqBS_12
              ( MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
                  (coe MAlonzo.Code.Peras.QQCD.Types.d_parent_70 (coe v2))
              )
              ( MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
                  ( coe
                      MAlonzo.Code.Peras.QQCD.Types.d_certificateBlock_106
                      (coe v1)
                  )
              )
        )
    )
    ( coe
        du_dropUntilBlock_212
        (coe MAlonzo.Code.Peras.QQCD.Types.d_slot_66 (coe v0))
        ( coe
            MAlonzo.Code.Haskell.Prim.du__'8728'__28
            (coe MAlonzo.Code.Peras.QQCD.Crypto.du_castHash_108)
            ( coe
                MAlonzo.Code.Haskell.Prim.du__'8728'__28
                ( coe
                    MAlonzo.Code.Haskell.Prim.du__'8728'__28
                    (coe MAlonzo.Code.Peras.QQCD.Crypto.du_castHash_108)
                    ( coe
                        MAlonzo.Code.Haskell.Prim.du__'8728'__28
                        ( coe
                            MAlonzo.Code.Haskell.Prim.du__'8728'__28
                            (coe MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24)
                            (coe MAlonzo.Code.Peras.QQCD.Crypto.d_primHashBytes_46)
                        )
                        ( coe
                            ( \v2 ->
                                MAlonzo.Code.Peras.QQCD.Types.d_signatureBytes_26 (coe v2)
                            )
                        )
                    )
                )
                ( coe
                    (\v2 -> MAlonzo.Code.Peras.QQCD.Types.d_signature_76 (coe v2))
                )
            )
            (coe v0)
        )
    )

-- Peras.QCD.Node.Specification.afterCooldown
d_afterCooldown_232 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46 ->
  Bool
d_afterCooldown_232 v0 v1 v2 =
  coe d_go_244 (coe v0) (coe v1) (coe v2) (coe (1 :: Integer))

-- Peras.QCD.Node.Specification._.go
d_go_244 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46 ->
  Integer ->
  Bool
d_go_244 v0 v1 v2 v3 =
  coe
    MAlonzo.Code.Haskell.Prim.du_case_of__58
    ( coe
        MAlonzo.Code.Haskell.Prim.Ord.d_compare_56
        MAlonzo.Code.Haskell.Prim.Ord.d_iOrdNat_246
        v0
        ( addInt
            (coe MAlonzo.Code.Peras.QQCD.Types.d_certificateRound_104 (coe v2))
            (coe mulInt (coe v3) (coe v1))
        )
    )
    ( \v4 v5 ->
        coe
          du_'46'extendedlambda0_248
          (coe v0)
          (coe v1)
          (coe v2)
          (coe v3)
          v4
    )

-- Peras.QCD.Node.Specification._..extendedlambda0
d_'46'extendedlambda0_248 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46 ->
  Integer ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ordering_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool
d_'46'extendedlambda0_248 v0 v1 v2 v3 v4 ~v5 =
  du_'46'extendedlambda0_248 v0 v1 v2 v3 v4
du_'46'extendedlambda0_248 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46 ->
  Integer ->
  MAlonzo.Code.Haskell.Prim.Ord.T_Ordering_6 ->
  Bool
du_'46'extendedlambda0_248 v0 v1 v2 v3 v4 =
  case coe v4 of
    MAlonzo.Code.Haskell.Prim.Ord.C_LT_8 ->
      coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
    MAlonzo.Code.Haskell.Prim.Ord.C_EQ_10 ->
      coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
    MAlonzo.Code.Haskell.Prim.Ord.C_GT_12 ->
      coe
        d_go_244
        (coe v0)
        (coe v1)
        (coe v2)
        (coe addInt (coe (1 :: Integer)) (coe v3))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Node.Specification.voting
d_voting_250 :: Integer -> MAlonzo.Code.Peras.QQCD.State.T_State_10
d_voting_250 v0 =
  coe
    MAlonzo.Code.Peras.QQCD.State.du_bindState_114
    (coe MAlonzo.Code.Peras.QQCD.Node.Preagreement.d_preagreement_8)
    ( coe
        ( \v1 ->
            coe
              MAlonzo.Code.Haskell.Prim.du_case_of__58
              (coe v1)
              ( coe
                  ( \v2 v3 ->
                      case coe v2 of
                        MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16 ->
                          coe MAlonzo.Code.Peras.QQCD.Node.Model.d_diffuse_124
                        MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 v4 ->
                          coe
                            MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                            ( coe
                                MAlonzo.Code.Peras.QQCD.State.du_use_260
                                ( coe
                                    ( \v5 v6 ->
                                        coe
                                          MAlonzo.Code.Peras.QQCD.Node.Model.du_currentRound_74
                                          (coe v6)
                                    )
                                )
                            )
                            ( coe
                                ( \v5 ->
                                    coe
                                      MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                      ( coe
                                          MAlonzo.Code.Peras.QQCD.Node.Model.d_peras_58
                                          (coe MAlonzo.Code.Peras.QQCD.Protocol.C_R_20)
                                      )
                                      ( coe
                                          ( \v6 ->
                                              coe
                                                MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                                ( coe
                                                    MAlonzo.Code.Peras.QQCD.Node.Model.d_peras_58
                                                    (coe MAlonzo.Code.Peras.QQCD.Protocol.C_K_22)
                                                )
                                                ( coe
                                                    ( \v7 ->
                                                        coe
                                                          MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                                          ( coe
                                                              MAlonzo.Code.Peras.QQCD.Util.du__'8649'__26
                                                              ( coe
                                                                  MAlonzo.Code.Peras.QQCD.State.du_iFunctorState_152
                                                              )
                                                              ( coe
                                                                  MAlonzo.Code.Peras.QQCD.State.du_use_260
                                                                  ( coe
                                                                      ( \v8 v9 ->
                                                                          coe
                                                                            MAlonzo.Code.Peras.QQCD.Node.Model.du_latestCertSeen_104
                                                                            (coe v9)
                                                                      )
                                                                  )
                                                              )
                                                              (coe du_oneRoundOld_258 (coe v5))
                                                          )
                                                          ( coe
                                                              ( \v8 ->
                                                                  coe
                                                                    MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                                                    ( coe
                                                                        MAlonzo.Code.Peras.QQCD.State.du_apState_94
                                                                        ( coe
                                                                            MAlonzo.Code.Haskell.Prim.Functor.d__'60''36''62'__26
                                                                            ( coe
                                                                                MAlonzo.Code.Peras.QQCD.State.du_iFunctorState_152
                                                                            )
                                                                            erased
                                                                            erased
                                                                            (d_extends_202 (coe v4))
                                                                            ( coe
                                                                                MAlonzo.Code.Peras.QQCD.State.du_use_260
                                                                                ( coe
                                                                                    ( \v9 v10 ->
                                                                                        coe
                                                                                          MAlonzo.Code.Peras.QQCD.Node.Model.du_latestCertSeen_104
                                                                                          (coe v10)
                                                                                    )
                                                                                )
                                                                            )
                                                                        )
                                                                        ( coe
                                                                            MAlonzo.Code.Peras.QQCD.State.du_use_260
                                                                            ( coe
                                                                                ( \v9 v10 ->
                                                                                    coe
                                                                                      MAlonzo.Code.Peras.QQCD.Node.Model.du_chains_86
                                                                                      (coe v10)
                                                                                )
                                                                            )
                                                                        )
                                                                    )
                                                                    ( coe
                                                                        ( \v9 ->
                                                                            coe
                                                                              MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                                                              ( coe
                                                                                  MAlonzo.Code.Peras.QQCD.Util.du__'8649'__26
                                                                                  ( coe
                                                                                      MAlonzo.Code.Peras.QQCD.State.du_iFunctorState_152
                                                                                  )
                                                                                  ( coe
                                                                                      MAlonzo.Code.Peras.QQCD.State.du_use_260
                                                                                      ( coe
                                                                                          ( \v10 v11 ->
                                                                                              coe
                                                                                                MAlonzo.Code.Peras.QQCD.Node.Model.du_latestCertSeen_104
                                                                                                (coe v11)
                                                                                          )
                                                                                      )
                                                                                  )
                                                                                  ( coe
                                                                                      du_inChainIgnorance_264
                                                                                      (coe v5)
                                                                                      (coe v6)
                                                                                  )
                                                                              )
                                                                              ( coe
                                                                                  ( \v10 ->
                                                                                      coe
                                                                                        MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                                                                        ( coe
                                                                                            MAlonzo.Code.Peras.QQCD.Util.du__'8649'__26
                                                                                            ( coe
                                                                                                MAlonzo.Code.Peras.QQCD.State.du_iFunctorState_152
                                                                                            )
                                                                                            ( coe
                                                                                                MAlonzo.Code.Peras.QQCD.State.du_use_260
                                                                                                ( coe
                                                                                                    ( \v11 v12 ->
                                                                                                        coe
                                                                                                          MAlonzo.Code.Peras.QQCD.Node.Model.du_latestCertOnChain_110
                                                                                                          ( coe
                                                                                                              v12
                                                                                                          )
                                                                                                    )
                                                                                                )
                                                                                            )
                                                                                            ( coe
                                                                                                d_afterCooldown_232
                                                                                                (coe v5)
                                                                                                (coe v7)
                                                                                            )
                                                                                        )
                                                                                        ( coe
                                                                                            ( \v11 ->
                                                                                                coe
                                                                                                  MAlonzo.Code.Haskell.Prim.du_if_then_else__68
                                                                                                  ( coe
                                                                                                      MAlonzo.Code.Haskell.Prim.Bool.d__'124''124'__10
                                                                                                      ( coe
                                                                                                          MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                                                                                                          (coe v8)
                                                                                                          (coe v9)
                                                                                                      )
                                                                                                      ( coe
                                                                                                          MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                                                                                                          (coe v10)
                                                                                                          ( coe
                                                                                                              v11
                                                                                                          )
                                                                                                      )
                                                                                                  )
                                                                                                  ( coe
                                                                                                      ( \v12 ->
                                                                                                          coe
                                                                                                            MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                                                                                            ( coe
                                                                                                                MAlonzo.Code.Peras.QQCD.State.du_apState_94
                                                                                                                ( coe
                                                                                                                    MAlonzo.Code.Peras.QQCD.State.du_apState_94
                                                                                                                    ( coe
                                                                                                                        MAlonzo.Code.Haskell.Prim.Functor.du__'60''36''62'__46
                                                                                                                        ( coe
                                                                                                                            MAlonzo.Code.Haskell.Prim.Functor.C_DefaultFunctor'46'constructor_1081
                                                                                                                            ( \v13
                                                                                                                               v14
                                                                                                                               v15
                                                                                                                               v16 ->
                                                                                                                                  coe
                                                                                                                                    MAlonzo.Code.Peras.QQCD.State.du_fmapState_68
                                                                                                                                    v15
                                                                                                                                    v16
                                                                                                                            )
                                                                                                                        )
                                                                                                                        ( MAlonzo.Code.Peras.QQCD.Crypto.Placeholders.d_signVote_26
                                                                                                                            ( coe
                                                                                                                                v5
                                                                                                                            )
                                                                                                                        )
                                                                                                                        ( coe
                                                                                                                            MAlonzo.Code.Peras.QQCD.State.du_use_260
                                                                                                                            ( coe
                                                                                                                                ( \v13
                                                                                                                                   v14 ->
                                                                                                                                      coe
                                                                                                                                        MAlonzo.Code.Peras.QQCD.Node.Model.du_creatorId_62
                                                                                                                                        ( coe
                                                                                                                                            v14
                                                                                                                                        )
                                                                                                                                )
                                                                                                                            )
                                                                                                                        )
                                                                                                                    )
                                                                                                                    ( coe
                                                                                                                        MAlonzo.Code.Peras.QQCD.State.du_pureState_82
                                                                                                                        ( coe
                                                                                                                            v0
                                                                                                                        )
                                                                                                                    )
                                                                                                                )
                                                                                                                ( coe
                                                                                                                    MAlonzo.Code.Peras.QQCD.State.du_pureState_82
                                                                                                                    ( coe
                                                                                                                        v4
                                                                                                                    )
                                                                                                                )
                                                                                                            )
                                                                                                            ( coe
                                                                                                                ( \v13 ->
                                                                                                                    coe
                                                                                                                      MAlonzo.Code.Peras.QQCD.State.du_bindState_114
                                                                                                                      ( coe
                                                                                                                          MAlonzo.Code.Peras.QQCD.State.du__'8789'__332
                                                                                                                          ( \v14
                                                                                                                             v15 ->
                                                                                                                                coe
                                                                                                                                  MAlonzo.Code.Peras.QQCD.Node.Model.du_votes_92
                                                                                                                                  ( coe
                                                                                                                                      v15
                                                                                                                                  )
                                                                                                                          )
                                                                                                                          ( \v14 ->
                                                                                                                              coe
                                                                                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                ( coe
                                                                                                                                    v13
                                                                                                                                )
                                                                                                                                ( coe
                                                                                                                                    v14
                                                                                                                                )
                                                                                                                          )
                                                                                                                      )
                                                                                                                      ( coe
                                                                                                                          ( \v14 ->
                                                                                                                              coe
                                                                                                                                MAlonzo.Code.Peras.QQCD.Util.du__'8606'__96
                                                                                                                                ( coe
                                                                                                                                    MAlonzo.Code.Peras.QQCD.State.du_iApplicativeState_156
                                                                                                                                )
                                                                                                                                ( coe
                                                                                                                                    MAlonzo.Code.Peras.QQCD.Node.Model.d_diffuse_124
                                                                                                                                )
                                                                                                                                ( coe
                                                                                                                                    MAlonzo.Code.Peras.QQCD.Types.C_NewVote_158
                                                                                                                                    ( coe
                                                                                                                                        v13
                                                                                                                                    )
                                                                                                                                )
                                                                                                                          )
                                                                                                                      )
                                                                                                                )
                                                                                                            )
                                                                                                      )
                                                                                                  )
                                                                                                  ( coe
                                                                                                      ( \v12 ->
                                                                                                          MAlonzo.Code.Peras.QQCD.Node.Model.d_diffuse_124
                                                                                                      )
                                                                                                  )
                                                                                            )
                                                                                        )
                                                                                  )
                                                                              )
                                                                        )
                                                                    )
                                                              )
                                                          )
                                                    )
                                                )
                                          )
                                      )
                                )
                            )
                        _ -> MAlonzo.RTE.mazUnreachableError
                  )
              )
        )
    )

-- Peras.QCD.Node.Specification._.oneRoundOld
d_oneRoundOld_258 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46 ->
  Bool
d_oneRoundOld_258 ~v0 v1 v2 = du_oneRoundOld_258 v1 v2
du_oneRoundOld_258 ::
  Integer -> MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46 -> Bool
du_oneRoundOld_258 v0 v1 =
  coe
    eqInt
    ( coe
        addInt
        (coe (1 :: Integer))
        ( coe
            MAlonzo.Code.Peras.QQCD.Types.d_certificateRound_104
            (coe v1)
        )
    )
    (coe v0)

-- Peras.QCD.Node.Specification._.inChainIgnorance
d_inChainIgnorance_264 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46 ->
  Bool
d_inChainIgnorance_264 ~v0 v1 v2 v3 =
  du_inChainIgnorance_264 v1 v2 v3
du_inChainIgnorance_264 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46 ->
  Bool
du_inChainIgnorance_264 v0 v1 v2 =
  coe
    MAlonzo.Code.Haskell.Prim.Ord.d__'62''61'__62
    MAlonzo.Code.Haskell.Prim.Ord.d_iOrdNat_246
    v0
    ( addInt
        (coe MAlonzo.Code.Peras.QQCD.Types.d_certificateRound_104 (coe v2))
        (coe v1)
    )
