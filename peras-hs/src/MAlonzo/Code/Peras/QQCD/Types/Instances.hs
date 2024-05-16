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

module MAlonzo.Code.Peras.QQCD.Types.Instances where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Haskell.Prim
import qualified MAlonzo.Code.Haskell.Prim.Bool
import qualified MAlonzo.Code.Haskell.Prim.Eq
import qualified MAlonzo.Code.Peras.QQCD.Crypto
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

-- Peras.QCD.Types.Instances.iMembershipProofEq
d_iMembershipProofEq_8 :: MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
d_iMembershipProofEq_8 =
  coe
    MAlonzo.Code.Haskell.Prim.Eq.C_Eq'46'constructor_7
    ( coe
        MAlonzo.Code.Peras.QQCD.Util.du_eqByBS_16
        ( coe
            ( \v0 ->
                MAlonzo.Code.Peras.QQCD.Types.d_membershipProofBytes_10 (coe v0)
            )
        )
    )

-- Peras.QCD.Types.Instances.iMembershipProofHashable
d_iMembershipProofHashable_10 ::
  MAlonzo.Code.Peras.QQCD.Crypto.T_Hashable_34
d_iMembershipProofHashable_10 =
  coe
    MAlonzo.Code.Peras.QQCD.Crypto.C_Hashable'46'constructor_187
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
                ( \v0 ->
                    MAlonzo.Code.Peras.QQCD.Types.d_membershipProofBytes_10
                      (coe v0)
                )
            )
        )
    )

-- Peras.QCD.Types.Instances.iLeadershipProofEq
d_iLeadershipProofEq_12 :: MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
d_iLeadershipProofEq_12 =
  coe
    MAlonzo.Code.Haskell.Prim.Eq.C_Eq'46'constructor_7
    ( coe
        MAlonzo.Code.Peras.QQCD.Util.du_eqByBS_16
        ( coe
            ( \v0 ->
                MAlonzo.Code.Peras.QQCD.Types.d_leadershipProofBytes_18 (coe v0)
            )
        )
    )

-- Peras.QCD.Types.Instances.iLeadershipProofHashable
d_iLeadershipProofHashable_14 ::
  MAlonzo.Code.Peras.QQCD.Crypto.T_Hashable_34
d_iLeadershipProofHashable_14 =
  coe
    MAlonzo.Code.Peras.QQCD.Crypto.C_Hashable'46'constructor_187
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
                ( \v0 ->
                    MAlonzo.Code.Peras.QQCD.Types.d_leadershipProofBytes_18
                      (coe v0)
                )
            )
        )
    )

-- Peras.QCD.Types.Instances.iSignatureEq
d_iSignatureEq_16 :: MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
d_iSignatureEq_16 =
  coe
    MAlonzo.Code.Haskell.Prim.Eq.C_Eq'46'constructor_7
    ( coe
        MAlonzo.Code.Peras.QQCD.Util.du_eqByBS_16
        ( coe
            ( \v0 ->
                MAlonzo.Code.Peras.QQCD.Types.d_signatureBytes_26 (coe v0)
            )
        )
    )

-- Peras.QCD.Types.Instances.iSignatureHashable
d_iSignatureHashable_18 ::
  MAlonzo.Code.Peras.QQCD.Crypto.T_Hashable_34
d_iSignatureHashable_18 =
  coe
    MAlonzo.Code.Peras.QQCD.Crypto.C_Hashable'46'constructor_187
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
                ( \v0 ->
                    MAlonzo.Code.Peras.QQCD.Types.d_signatureBytes_26 (coe v0)
                )
            )
        )
    )

-- Peras.QCD.Types.Instances.iVerificationKeyEq
d_iVerificationKeyEq_20 :: MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
d_iVerificationKeyEq_20 =
  coe
    MAlonzo.Code.Haskell.Prim.Eq.C_Eq'46'constructor_7
    ( coe
        MAlonzo.Code.Peras.QQCD.Util.du_eqByBS_16
        ( coe
            ( \v0 ->
                MAlonzo.Code.Peras.QQCD.Types.d_verificationKeyBytes_34 (coe v0)
            )
        )
    )

-- Peras.QCD.Types.Instances.iVerificationKeyHashable
d_iVerificationKeyHashable_22 ::
  MAlonzo.Code.Peras.QQCD.Crypto.T_Hashable_34
d_iVerificationKeyHashable_22 =
  coe
    MAlonzo.Code.Peras.QQCD.Crypto.C_Hashable'46'constructor_187
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
                ( \v0 ->
                    MAlonzo.Code.Peras.QQCD.Types.d_verificationKeyBytes_34
                      (coe v0)
                )
            )
        )
    )

-- Peras.QCD.Types.Instances.iVoteEq
d_iVoteEq_24 :: MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
d_iVoteEq_24 =
  coe
    MAlonzo.Code.Haskell.Prim.Eq.C_Eq'46'constructor_7
    ( coe
        ( \v0 v1 ->
            MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
              ( coe
                  MAlonzo.Code.Peras.QQCD.Util.du_eqBy_8
                  (coe MAlonzo.Code.Haskell.Prim.Eq.d_iEqNat_28)
                  ( coe
                      (\v2 -> MAlonzo.Code.Peras.QQCD.Types.d_voteRound_140 (coe v2))
                  )
                  (coe v0)
                  (coe v1)
              )
              ( coe
                  MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                  ( coe
                      MAlonzo.Code.Peras.QQCD.Util.du_eqBy_8
                      (coe d_iVerificationKeyEq_20)
                      ( coe
                          (\v2 -> MAlonzo.Code.Peras.QQCD.Types.d_voteParty_142 (coe v2))
                      )
                      (coe v0)
                      (coe v1)
                  )
                  ( coe
                      MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                      ( coe
                          MAlonzo.Code.Peras.QQCD.Util.du_eqBy_8
                          (coe MAlonzo.Code.Peras.QQCD.Crypto.du_iHashEq_26)
                          ( coe
                              (\v2 -> MAlonzo.Code.Peras.QQCD.Types.d_voteBlock_146 (coe v2))
                          )
                          (coe v0)
                          (coe v1)
                      )
                      ( coe
                          MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                          ( coe
                              MAlonzo.Code.Peras.QQCD.Util.du_eqBy_8
                              (coe d_iMembershipProofEq_8)
                              ( coe
                                  (\v2 -> MAlonzo.Code.Peras.QQCD.Types.d_voteProof_148 (coe v2))
                              )
                              (coe v0)
                              (coe v1)
                          )
                          ( coe
                              MAlonzo.Code.Peras.QQCD.Util.du_eqBy_8
                              (coe d_iSignatureEq_16)
                              ( coe
                                  ( \v2 ->
                                      MAlonzo.Code.Peras.QQCD.Types.d_voteSignature_150 (coe v2)
                                  )
                              )
                              (coe v0)
                              (coe v1)
                          )
                      )
                  )
              )
        )
    )

-- Peras.QCD.Types.Instances.iVoteHashable
d_iVoteHashable_30 :: MAlonzo.Code.Peras.QQCD.Crypto.T_Hashable_34
d_iVoteHashable_30 =
  coe
    MAlonzo.Code.Peras.QQCD.Crypto.C_Hashable'46'constructor_187
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
                        ( \v0 ->
                            MAlonzo.Code.Peras.QQCD.Types.d_membershipProofBytes_10
                              (coe v0)
                        )
                    )
                )
            )
            ( coe
                (\v0 -> MAlonzo.Code.Peras.QQCD.Types.d_voteProof_148 (coe v0))
            )
        )
    )

-- Peras.QCD.Types.Instances.iCertificateEq
d_iCertificateEq_32 :: MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
d_iCertificateEq_32 =
  coe
    MAlonzo.Code.Haskell.Prim.Eq.C_Eq'46'constructor_7
    ( coe
        ( \v0 v1 ->
            MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
              ( coe
                  MAlonzo.Code.Peras.QQCD.Util.du_eqBy_8
                  (coe MAlonzo.Code.Haskell.Prim.Eq.d_iEqNat_28)
                  ( coe
                      ( \v2 ->
                          MAlonzo.Code.Peras.QQCD.Types.d_certificateRound_104 (coe v2)
                      )
                  )
                  (coe v0)
                  (coe v1)
              )
              ( coe
                  MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                  ( coe
                      MAlonzo.Code.Peras.QQCD.Util.du_eqBy_8
                      (coe MAlonzo.Code.Peras.QQCD.Crypto.du_iHashEq_26)
                      ( coe
                          ( \v2 ->
                              MAlonzo.Code.Peras.QQCD.Types.d_certificateBlock_106 (coe v2)
                          )
                      )
                      (coe v0)
                      (coe v1)
                  )
                  ( coe
                      MAlonzo.Code.Peras.QQCD.Util.du_eqByBS_16
                      ( coe
                          ( \v2 ->
                              MAlonzo.Code.Peras.QQCD.Types.d_certificateBytes_108 (coe v2)
                          )
                      )
                      (coe v0)
                      (coe v1)
                  )
              )
        )
    )

-- Peras.QCD.Types.Instances.iCertificateHashable
d_iCertificateHashable_38 ::
  MAlonzo.Code.Peras.QQCD.Crypto.T_Hashable_34
d_iCertificateHashable_38 =
  coe
    MAlonzo.Code.Peras.QQCD.Crypto.C_Hashable'46'constructor_187
    ( coe
        ( \v0 ->
            coe
              MAlonzo.Code.Haskell.Prim.du__'36'__48
              (coe MAlonzo.Code.Peras.QQCD.Crypto.du_castHash_108)
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
                                  ( coe
                                      MAlonzo.Code.Peras.QQCD.Types.d_certificateRound_104
                                      (coe v0)
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
                                          (\v1 -> MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22 (coe v1))
                                      )
                                      ( coe
                                          MAlonzo.Code.Peras.QQCD.Types.d_certificateBlock_106
                                          (coe v0)
                                      )
                                  )
                              )
                              ( coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  ( coe
                                      MAlonzo.Code.Peras.QQCD.Crypto.d_hashBytes_22
                                      ( coe
                                          MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                          (coe MAlonzo.Code.Peras.QQCD.Crypto.C_MakeHash_24)
                                          (coe MAlonzo.Code.Peras.QQCD.Crypto.d_primHashBytes_46)
                                          ( coe
                                              MAlonzo.Code.Peras.QQCD.Types.d_certificateBytes_108
                                              (coe v0)
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

-- Peras.QCD.Types.Instances.iBlockEq
d_iBlockEq_42 :: MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
d_iBlockEq_42 =
  coe
    MAlonzo.Code.Haskell.Prim.Eq.C_Eq'46'constructor_7
    ( coe
        ( \v0 v1 ->
            MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
              ( coe
                  MAlonzo.Code.Peras.QQCD.Util.du_eqBy_8
                  (coe MAlonzo.Code.Haskell.Prim.Eq.d_iEqNat_28)
                  (coe (\v2 -> MAlonzo.Code.Peras.QQCD.Types.d_slot_66 (coe v2)))
                  (coe v0)
                  (coe v1)
              )
              ( coe
                  MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                  ( coe
                      MAlonzo.Code.Peras.QQCD.Util.du_eqBy_8
                      (coe d_iVerificationKeyEq_20)
                      (coe (\v2 -> MAlonzo.Code.Peras.QQCD.Types.d_creator_68 (coe v2)))
                      (coe v0)
                      (coe v1)
                  )
                  ( coe
                      MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                      ( coe
                          MAlonzo.Code.Peras.QQCD.Util.du_eqBy_8
                          (coe MAlonzo.Code.Peras.QQCD.Crypto.du_iHashEq_26)
                          (coe (\v2 -> MAlonzo.Code.Peras.QQCD.Types.d_parent_70 (coe v2)))
                          (coe v0)
                          (coe v1)
                      )
                      ( coe
                          MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                          ( coe
                              MAlonzo.Code.Peras.QQCD.Util.du_eqBy_8
                              ( coe
                                  MAlonzo.Code.Haskell.Prim.Eq.du_iEqMaybe_86
                                  (coe d_iCertificateEq_32)
                              )
                              ( coe
                                  (\v2 -> MAlonzo.Code.Peras.QQCD.Types.d_certificate_72 (coe v2))
                              )
                              (coe v0)
                              (coe v1)
                          )
                          ( coe
                              MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                              ( coe
                                  MAlonzo.Code.Peras.QQCD.Util.du_eqBy_8
                                  (coe d_iLeadershipProofEq_12)
                                  ( coe
                                      ( \v2 ->
                                          MAlonzo.Code.Peras.QQCD.Types.d_leadershipProof_74 (coe v2)
                                      )
                                  )
                                  (coe v0)
                                  (coe v1)
                              )
                              ( coe
                                  MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                                  ( coe
                                      MAlonzo.Code.Peras.QQCD.Util.du_eqBy_8
                                      (coe d_iSignatureEq_16)
                                      ( coe
                                          (\v2 -> MAlonzo.Code.Peras.QQCD.Types.d_signature_76 (coe v2))
                                      )
                                      (coe v0)
                                      (coe v1)
                                  )
                                  ( coe
                                      MAlonzo.Code.Peras.QQCD.Util.du_eqBy_8
                                      (coe MAlonzo.Code.Peras.QQCD.Crypto.du_iHashEq_26)
                                      ( coe
                                          (\v2 -> MAlonzo.Code.Peras.QQCD.Types.d_bodyHash_78 (coe v2))
                                      )
                                      (coe v0)
                                      (coe v1)
                                  )
                              )
                          )
                      )
                  )
              )
        )
    )

-- Peras.QCD.Types.Instances.iBlockHashable
d_iBlockHashable_48 :: MAlonzo.Code.Peras.QQCD.Crypto.T_Hashable_34
d_iBlockHashable_48 =
  coe
    MAlonzo.Code.Peras.QQCD.Crypto.C_Hashable'46'constructor_187
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
                        ( \v0 ->
                            MAlonzo.Code.Peras.QQCD.Types.d_signatureBytes_26 (coe v0)
                        )
                    )
                )
            )
            ( coe
                (\v0 -> MAlonzo.Code.Peras.QQCD.Types.d_signature_76 (coe v0))
            )
        )
    )

-- Peras.QCD.Types.Instances.iBlockBodyEq
d_iBlockBodyEq_50 :: MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
d_iBlockBodyEq_50 =
  coe
    MAlonzo.Code.Haskell.Prim.Eq.C_Eq'46'constructor_7
    ( coe
        ( \v0 v1 ->
            MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
              ( coe
                  MAlonzo.Code.Peras.QQCD.Util.du_eqBy_8
                  (coe MAlonzo.Code.Peras.QQCD.Crypto.du_iHashEq_26)
                  ( coe
                      (\v2 -> MAlonzo.Code.Peras.QQCD.Types.d_headerHash_88 (coe v2))
                  )
                  (coe v0)
                  (coe v1)
              )
              ( coe
                  MAlonzo.Code.Peras.QQCD.Util.du_eqBy_8
                  ( coe
                      MAlonzo.Code.Haskell.Prim.Eq.du_iEqList_68
                      (coe MAlonzo.Code.Haskell.Prim.Eq.d_iEqUnit_42)
                  )
                  (coe (\v2 -> MAlonzo.Code.Peras.QQCD.Types.d_payload_90 (coe v2)))
                  (coe v0)
                  (coe v1)
              )
        )
    )

-- Peras.QCD.Types.Instances.tipHash
d_tipHash_56 ::
  [MAlonzo.Code.Peras.QQCD.Types.T_Block_50] ->
  MAlonzo.Code.Peras.QQCD.Crypto.T_Hash_16
d_tipHash_56 v0 =
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

-- Peras.QCD.Types.Instances.iMessageEq
d_iMessageEq_60 :: MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
d_iMessageEq_60 =
  coe
    MAlonzo.Code.Haskell.Prim.Eq.C_Eq'46'constructor_7
    ( coe
        ( \v0 ->
            case coe v0 of
              MAlonzo.Code.Peras.QQCD.Types.C_NewChain_156 v1 ->
                coe
                  ( \v2 ->
                      let v3 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                       in coe
                            ( case coe v2 of
                                MAlonzo.Code.Peras.QQCD.Types.C_NewChain_156 v4 ->
                                  coe
                                    MAlonzo.Code.Haskell.Prim.Eq.du_eqList_76
                                    (coe d_iBlockEq_42)
                                    (coe v1)
                                    (coe v4)
                                _ -> coe v3
                            )
                  )
              MAlonzo.Code.Peras.QQCD.Types.C_NewVote_158 v1 ->
                coe
                  ( \v2 ->
                      let v3 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                       in coe
                            ( case coe v2 of
                                MAlonzo.Code.Peras.QQCD.Types.C_NewVote_158 v4 ->
                                  coe
                                    MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                                    ( coe
                                        MAlonzo.Code.Peras.QQCD.Util.du_eqBy_8
                                        (coe MAlonzo.Code.Haskell.Prim.Eq.d_iEqNat_28)
                                        ( coe
                                            ( \v5 ->
                                                MAlonzo.Code.Peras.QQCD.Types.d_voteRound_140
                                                  (coe v5)
                                            )
                                        )
                                        (coe v1)
                                        (coe v4)
                                    )
                                    ( coe
                                        MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                                        ( coe
                                            MAlonzo.Code.Peras.QQCD.Util.du_eqBy_8
                                            (coe d_iVerificationKeyEq_20)
                                            ( coe
                                                ( \v5 ->
                                                    MAlonzo.Code.Peras.QQCD.Types.d_voteParty_142
                                                      (coe v5)
                                                )
                                            )
                                            (coe v1)
                                            (coe v4)
                                        )
                                        ( coe
                                            MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                                            ( coe
                                                MAlonzo.Code.Peras.QQCD.Util.du_eqBy_8
                                                (coe MAlonzo.Code.Peras.QQCD.Crypto.du_iHashEq_26)
                                                ( coe
                                                    ( \v5 ->
                                                        MAlonzo.Code.Peras.QQCD.Types.d_voteBlock_146
                                                          (coe v5)
                                                    )
                                                )
                                                (coe v1)
                                                (coe v4)
                                            )
                                            ( coe
                                                MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                                                ( coe
                                                    MAlonzo.Code.Peras.QQCD.Util.du_eqBy_8
                                                    (coe d_iMembershipProofEq_8)
                                                    ( coe
                                                        ( \v5 ->
                                                            MAlonzo.Code.Peras.QQCD.Types.d_voteProof_148
                                                              (coe v5)
                                                        )
                                                    )
                                                    (coe v1)
                                                    (coe v4)
                                                )
                                                ( coe
                                                    MAlonzo.Code.Peras.QQCD.Util.du_eqBy_8
                                                    (coe d_iSignatureEq_16)
                                                    ( coe
                                                        ( \v5 ->
                                                            MAlonzo.Code.Peras.QQCD.Types.d_voteSignature_150
                                                              (coe v5)
                                                        )
                                                    )
                                                    (coe v1)
                                                    (coe v4)
                                                )
                                            )
                                        )
                                    )
                                _ -> coe v3
                            )
                  )
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )
