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

module MAlonzo.Code.Peras.QQCD.Crypto.Placeholders where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Haskell.Prim
import qualified MAlonzo.Code.Haskell.Prim.List
import qualified MAlonzo.Code.Haskell.Prim.Maybe
import qualified MAlonzo.Code.Peras.QQCD.Crypto
import qualified MAlonzo.Code.Peras.QQCD.Types
import qualified MAlonzo.Code.Peras.QQCD.Types.Instances
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

-- Peras.QCD.Crypto.Placeholders.proveLeader
d_proveLeader_8 ::
  Integer ->
  MAlonzo.Code.Peras.QQCD.Types.T_VerificationKey_30 ->
  MAlonzo.Code.Peras.QQCD.Types.T_LeadershipProof_14
d_proveLeader_8 v0 v1 =
  coe
    MAlonzo.Code.Peras.QQCD.Types.C_MakeLeadershipProof_20
    ( coe
        MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
        ( coe
            MAlonzo.Code.Haskell.Prim.du__'36'__48
            ( coe
                MAlonzo.Code.Haskell.Prim.du__'8728'__28
                (coe MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24)
                (coe MAlonzo.Code.Peras.QQCD.Crypto.d_primHashBytes_46)
            )
            ( coe
                MAlonzo.Code.Peras.QQCD.Crypto.d_concatBS_10
                ( coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    ( coe
                        MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
                        ( coe
                            MAlonzo.Code.Haskell.Prim.du__'8728'__28
                            (coe MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24)
                            (coe MAlonzo.Code.Peras.QQCD.Crypto.d_primHashNat_44)
                            (coe v0)
                        )
                    )
                    ( coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        ( coe
                            MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
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
                                            MAlonzo.Code.Peras.QQCD.Types.d_verificationKeyBytes_34
                                              (coe v2)
                                        )
                                    )
                                )
                                (coe v1)
                            )
                        )
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                    )
                )
            )
        )
    )

-- Peras.QCD.Crypto.Placeholders.signBlock
d_signBlock_14 ::
  Integer ->
  MAlonzo.Code.Peras.QQCD.Types.T_VerificationKey_30 ->
  MAlonzo.Code.Peras.QQCD.Crypto.T_Hash_16 ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10 ->
  [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6] ->
  MAlonzo.Code.Peras.QQCD.Types.T_Block_50
d_signBlock_14 v0 v1 v2 v3 v4 =
  coe
    MAlonzo.Code.Peras.QQCD.Types.C_MakeBlock_80
    (coe v0)
    (coe v1)
    (coe v2)
    (coe v3)
    (coe d_proveLeader_8 (coe v0) (coe v1))
    ( coe
        MAlonzo.Code.Peras.QQCD.Types.C_MakeSignature_28
        ( coe
            MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
            ( coe
                MAlonzo.Code.Haskell.Prim.du__'36'__48
                ( coe
                    MAlonzo.Code.Haskell.Prim.du__'8728'__28
                    (coe MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24)
                    (coe MAlonzo.Code.Peras.QQCD.Crypto.d_primHashBytes_46)
                )
                ( coe
                    MAlonzo.Code.Peras.QQCD.Crypto.d_concatBS_10
                    ( coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        ( coe
                            MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
                            ( coe
                                MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                ( coe
                                    MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                    (coe MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24)
                                    (coe MAlonzo.Code.Peras.QQCD.Crypto.d_primHashBytes_46)
                                )
                                ( coe
                                    (\v5 -> MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22 (coe v5))
                                )
                                ( coe
                                    MAlonzo.Code.Haskell.Prim.du__'36'__48
                                    ( coe
                                        MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                        (coe MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24)
                                        (coe MAlonzo.Code.Peras.QQCD.Crypto.d_primHashBytes_46)
                                    )
                                    ( coe
                                        MAlonzo.Code.Peras.QQCD.Crypto.d_concatBS_10
                                        ( coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            ( coe
                                                MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
                                                ( coe
                                                    MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                                    (coe MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24)
                                                    (coe MAlonzo.Code.Peras.QQCD.Crypto.d_primHashNat_44)
                                                    (coe v0)
                                                )
                                            )
                                            ( coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                ( coe
                                                    MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
                                                    ( coe
                                                        MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                                        (coe MAlonzo.Code.Peras.QQCD.Crypto.du_castHash_108)
                                                        ( coe
                                                            MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                                            ( coe
                                                                MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                                                ( coe
                                                                    MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24
                                                                )
                                                                ( coe
                                                                    MAlonzo.Code.Peras.QQCD.Crypto.d_primHashBytes_46
                                                                )
                                                            )
                                                            ( coe
                                                                ( \v5 ->
                                                                    MAlonzo.Code.Peras.QQCD.Types.d_verificationKeyBytes_34
                                                                      (coe v5)
                                                                )
                                                            )
                                                        )
                                                        (coe v1)
                                                    )
                                                )
                                                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                            )
                                        )
                                    )
                                )
                            )
                        )
                        ( coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            ( coe
                                MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
                                ( coe
                                    MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                    ( coe
                                        MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                        (coe MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24)
                                        (coe MAlonzo.Code.Peras.QQCD.Crypto.d_primHashBytes_46)
                                    )
                                    ( coe
                                        (\v5 -> MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22 (coe v5))
                                    )
                                    ( coe
                                        MAlonzo.Code.Haskell.Prim.du__'36'__48
                                        ( coe
                                            MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                            (coe MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24)
                                            (coe MAlonzo.Code.Peras.QQCD.Crypto.d_primHashBytes_46)
                                        )
                                        ( coe
                                            MAlonzo.Code.Peras.QQCD.Crypto.d_concatBS_10
                                            ( coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                ( coe
                                                    MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
                                                    ( coe
                                                        MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                                        ( coe
                                                            MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                                            (coe MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24)
                                                            ( coe
                                                                MAlonzo.Code.Peras.QQCD.Crypto.d_primHashBytes_46
                                                            )
                                                        )
                                                        ( coe
                                                            ( \v5 ->
                                                                MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
                                                                  (coe v5)
                                                            )
                                                        )
                                                        (coe v2)
                                                    )
                                                )
                                                ( coe
                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                    ( coe
                                                        MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
                                                        ( coe
                                                            MAlonzo.Code.Peras.QQCD.Crypto.d_hash_40
                                                            ( coe
                                                                MAlonzo.Code.Peras.QQCD.Crypto.du_iMaybeHashable_112
                                                                ( coe
                                                                    MAlonzo.Code.Peras.QQCD.Types.Instances.d_iCertificateHashable_38
                                                                )
                                                            )
                                                            v3
                                                        )
                                                    )
                                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                            ( coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                ( coe
                                    MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
                                    ( coe
                                        MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                        ( coe
                                            MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                            (coe MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24)
                                            (coe MAlonzo.Code.Peras.QQCD.Crypto.d_primHashBytes_46)
                                        )
                                        ( coe
                                            ( \v5 ->
                                                MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22 (coe v5)
                                            )
                                        )
                                        ( coe
                                            MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                            (coe MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24)
                                            ( coe
                                                MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                                (coe MAlonzo.Code.Peras.QQCD.Crypto.d_primHashBytes_46)
                                                ( coe
                                                    MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                                    (coe MAlonzo.Code.Peras.QQCD.Crypto.d_concatBS_10)
                                                    ( coe
                                                        MAlonzo.Code.Haskell.Prim.List.du_map_6
                                                        ( coe
                                                            ( \v5 ->
                                                                MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
                                                                  ( coe
                                                                      MAlonzo.Code.Haskell.Prim.du__'36'__48
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24
                                                                      )
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.QQCD.Crypto.d_primHashUnit_42
                                                                          ( coe
                                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                                                                          )
                                                                      )
                                                                  )
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                            (coe v4)
                                        )
                                    )
                                )
                                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                            )
                        )
                    )
                )
            )
        )
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        (coe MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24)
        ( coe
            MAlonzo.Code.Haskell.Prim.du__'8728'__28
            (coe MAlonzo.Code.Peras.QQCD.Crypto.d_primHashBytes_46)
            ( coe
                MAlonzo.Code.Haskell.Prim.du__'8728'__28
                (coe MAlonzo.Code.Peras.QQCD.Crypto.d_concatBS_10)
                ( coe
                    MAlonzo.Code.Haskell.Prim.List.du_map_6
                    ( coe
                        ( \v5 ->
                            MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
                              ( coe
                                  MAlonzo.Code.Haskell.Prim.du__'36'__48
                                  (coe MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24)
                                  ( coe
                                      MAlonzo.Code.Peras.QQCD.Crypto.d_primHashUnit_42
                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  )
                              )
                        )
                    )
                )
            )
        )
        (coe v4)
    )

-- Peras.QCD.Crypto.Placeholders.signVote
d_signVote_26 ::
  Integer ->
  MAlonzo.Code.Peras.QQCD.Types.T_VerificationKey_30 ->
  Integer ->
  MAlonzo.Code.Peras.QQCD.Types.T_Block_50 ->
  MAlonzo.Code.Peras.QQCD.Types.T_Vote_126
d_signVote_26 v0 v1 v2 v3 =
  coe
    MAlonzo.Code.Peras.QQCD.Types.C_MakeVote_152
    (coe v0)
    (coe v1)
    (coe v2)
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
                        ( \v4 ->
                            MAlonzo.Code.Peras.QQCD.Types.d_signatureBytes_26 (coe v4)
                        )
                    )
                )
            )
            ( coe
                (\v4 -> MAlonzo.Code.Peras.QQCD.Types.d_signature_76 (coe v4))
            )
        )
        (coe v3)
    )
    ( coe
        MAlonzo.Code.Peras.QQCD.Types.C_MakeMembershipProof_12
        ( coe
            MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
            ( coe
                MAlonzo.Code.Haskell.Prim.du__'36'__48
                ( coe
                    MAlonzo.Code.Haskell.Prim.du__'8728'__28
                    (coe MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24)
                    (coe MAlonzo.Code.Peras.QQCD.Crypto.d_primHashBytes_46)
                )
                ( coe
                    MAlonzo.Code.Peras.QQCD.Crypto.d_concatBS_10
                    ( coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        ( coe
                            MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
                            ( coe
                                MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                (coe MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24)
                                (coe MAlonzo.Code.Peras.QQCD.Crypto.d_primHashNat_44)
                                (coe v0)
                            )
                        )
                        ( coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            ( coe
                                MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
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
                                            ( \v4 ->
                                                MAlonzo.Code.Peras.QQCD.Types.d_verificationKeyBytes_34
                                                  (coe v4)
                                            )
                                        )
                                    )
                                    (coe v1)
                                )
                            )
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                        )
                    )
                )
            )
        )
    )
    ( coe
        MAlonzo.Code.Peras.QQCD.Types.C_MakeSignature_28
        ( coe
            MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
            ( coe
                MAlonzo.Code.Haskell.Prim.du__'36'__48
                ( coe
                    MAlonzo.Code.Haskell.Prim.du__'8728'__28
                    (coe MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24)
                    (coe MAlonzo.Code.Peras.QQCD.Crypto.d_primHashBytes_46)
                )
                ( coe
                    MAlonzo.Code.Peras.QQCD.Crypto.d_concatBS_10
                    ( coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        ( coe
                            MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
                            ( coe
                                MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                (coe MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24)
                                (coe MAlonzo.Code.Peras.QQCD.Crypto.d_primHashNat_44)
                                (coe v0)
                            )
                        )
                        ( coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            ( coe
                                MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
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
                                            ( \v4 ->
                                                MAlonzo.Code.Peras.QQCD.Types.d_verificationKeyBytes_34
                                                  (coe v4)
                                            )
                                        )
                                    )
                                    (coe v1)
                                )
                            )
                            ( coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                ( coe
                                    MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
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
                                                        ( coe
                                                            MAlonzo.Code.Peras.QQCD.Crypto.d_primHashBytes_46
                                                        )
                                                    )
                                                    ( coe
                                                        ( \v4 ->
                                                            MAlonzo.Code.Peras.QQCD.Types.d_signatureBytes_26
                                                              (coe v4)
                                                        )
                                                    )
                                                )
                                            )
                                            ( coe
                                                ( \v4 ->
                                                    MAlonzo.Code.Peras.QQCD.Types.d_signature_76 (coe v4)
                                                )
                                            )
                                        )
                                        (coe v3)
                                    )
                                )
                                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                            )
                        )
                    )
                )
            )
        )
    )

-- Peras.QCD.Crypto.Placeholders.buildCertificate
d_buildCertificate_36 ::
  [MAlonzo.Code.Peras.QQCD.Types.T_Vote_126] ->
  MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46
d_buildCertificate_36 v0 =
  coe
    MAlonzo.Code.Peras.QQCD.Types.C_MakeCertificate_110
    (coe du_getRound_44 (coe v0))
    (coe du_getBlock_48 (coe v0))
    ( coe
        MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
        ( coe
            MAlonzo.Code.Haskell.Prim.du__'8728'__28
            (coe MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24)
            ( coe
                MAlonzo.Code.Haskell.Prim.du__'8728'__28
                (coe MAlonzo.Code.Peras.QQCD.Crypto.d_primHashBytes_46)
                ( coe
                    MAlonzo.Code.Haskell.Prim.du__'8728'__28
                    (coe MAlonzo.Code.Peras.QQCD.Crypto.d_concatBS_10)
                    ( coe
                        MAlonzo.Code.Haskell.Prim.List.du_map_6
                        ( coe
                            ( \v1 ->
                                MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
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
                                                          MAlonzo.Code.Peras.QQCD.Types.d_membershipProofBytes_10
                                                            (coe v2)
                                                      )
                                                  )
                                              )
                                          )
                                          ( coe
                                              ( \v2 ->
                                                  MAlonzo.Code.Peras.QQCD.Types.d_voteProof_148 (coe v2)
                                              )
                                          )
                                      )
                                      (coe v1)
                                  )
                            )
                        )
                    )
                )
            )
            (coe v0)
        )
    )

-- Peras.QCD.Crypto.Placeholders._.getRound
d_getRound_44 ::
  [MAlonzo.Code.Peras.QQCD.Types.T_Vote_126] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Vote_126] ->
  Integer
d_getRound_44 ~v0 v1 = du_getRound_44 v1
du_getRound_44 ::
  [MAlonzo.Code.Peras.QQCD.Types.T_Vote_126] -> Integer
du_getRound_44 v0 =
  case coe v0 of
    [] -> coe (0 :: Integer)
    (:) v1 v2 ->
      coe MAlonzo.Code.Peras.QQCD.Types.d_voteRound_140 (coe v1)
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Crypto.Placeholders._.getBlock
d_getBlock_48 ::
  [MAlonzo.Code.Peras.QQCD.Types.T_Vote_126] ->
  [MAlonzo.Code.Peras.QQCD.Types.T_Vote_126] ->
  MAlonzo.Code.Peras.QQCD.Crypto.T_Hash_16
d_getBlock_48 ~v0 v1 = du_getBlock_48 v1
du_getBlock_48 ::
  [MAlonzo.Code.Peras.QQCD.Types.T_Vote_126] ->
  MAlonzo.Code.Peras.QQCD.Crypto.T_Hash_16
du_getBlock_48 v0 =
  case coe v0 of
    [] -> coe MAlonzo.Code.Peras.QQCD.Types.d_genesisHash_96
    (:) v1 v2 ->
      coe MAlonzo.Code.Peras.QQCD.Types.d_voteBlock_146 (coe v1)
    _ -> MAlonzo.RTE.mazUnreachableError
