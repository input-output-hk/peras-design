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

module MAlonzo.Code.Peras.QQCD.Node.Model where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Haskell.Prim.Functor
import qualified MAlonzo.Code.Peras.QQCD.Crypto
import qualified MAlonzo.Code.Peras.QQCD.Protocol
import qualified MAlonzo.Code.Peras.QQCD.State
import qualified MAlonzo.Code.Peras.QQCD.Types
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

-- Peras.QCD.Node.Model.NodeModel
d_NodeModel_8 = ()
data T_NodeModel_8
  = C_NodeModel'46'constructor_205
      MAlonzo.Code.Peras.QQCD.Protocol.T_Params_26
      MAlonzo.Code.Peras.QQCD.Types.T_VerificationKey_30
      Integer
      Integer
      [MAlonzo.Code.Peras.QQCD.Types.T_Block_50]
      [[MAlonzo.Code.Peras.QQCD.Types.T_Block_50]]
      [MAlonzo.Code.Peras.QQCD.Types.T_Vote_126]
      [MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46]
      MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46
      MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46

-- Peras.QCD.Node.Model.NodeModel.nodeProtocol
d_nodeProtocol_30 ::
  T_NodeModel_8 -> MAlonzo.Code.Peras.QQCD.Protocol.T_Params_26
d_nodeProtocol_30 v0 =
  case coe v0 of
    C_NodeModel'46'constructor_205 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ->
      coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Node.Model.NodeModel.nodeCreatorId
d_nodeCreatorId_32 ::
  T_NodeModel_8 -> MAlonzo.Code.Peras.QQCD.Types.T_VerificationKey_30
d_nodeCreatorId_32 v0 =
  case coe v0 of
    C_NodeModel'46'constructor_205 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ->
      coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Node.Model.NodeModel.nodeCurrentSlot
d_nodeCurrentSlot_34 :: T_NodeModel_8 -> Integer
d_nodeCurrentSlot_34 v0 =
  case coe v0 of
    C_NodeModel'46'constructor_205 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ->
      coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Node.Model.NodeModel.nodeCurrentRound
d_nodeCurrentRound_36 :: T_NodeModel_8 -> Integer
d_nodeCurrentRound_36 v0 =
  case coe v0 of
    C_NodeModel'46'constructor_205 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ->
      coe v4
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Node.Model.NodeModel.nodePreferredChain
d_nodePreferredChain_38 ::
  T_NodeModel_8 -> [MAlonzo.Code.Peras.QQCD.Types.T_Block_50]
d_nodePreferredChain_38 v0 =
  case coe v0 of
    C_NodeModel'46'constructor_205 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ->
      coe v5
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Node.Model.NodeModel.nodeChains
d_nodeChains_40 ::
  T_NodeModel_8 -> [[MAlonzo.Code.Peras.QQCD.Types.T_Block_50]]
d_nodeChains_40 v0 =
  case coe v0 of
    C_NodeModel'46'constructor_205 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ->
      coe v6
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Node.Model.NodeModel.nodeVotes
d_nodeVotes_42 ::
  T_NodeModel_8 -> [MAlonzo.Code.Peras.QQCD.Types.T_Vote_126]
d_nodeVotes_42 v0 =
  case coe v0 of
    C_NodeModel'46'constructor_205 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ->
      coe v7
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Node.Model.NodeModel.nodeCerts
d_nodeCerts_44 ::
  T_NodeModel_8 -> [MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46]
d_nodeCerts_44 v0 =
  case coe v0 of
    C_NodeModel'46'constructor_205 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ->
      coe v8
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Node.Model.NodeModel.nodeLatestCertSeen
d_nodeLatestCertSeen_46 ::
  T_NodeModel_8 -> MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46
d_nodeLatestCertSeen_46 v0 =
  case coe v0 of
    C_NodeModel'46'constructor_205 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ->
      coe v9
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Node.Model.NodeModel.nodeLatestCertOnChain
d_nodeLatestCertOnChain_48 ::
  T_NodeModel_8 -> MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46
d_nodeLatestCertOnChain_48 v0 =
  case coe v0 of
    C_NodeModel'46'constructor_205 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ->
      coe v10
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Node.Model.emptyNode
d_emptyNode_50 :: T_NodeModel_8
d_emptyNode_50 =
  coe
    C_NodeModel'46'constructor_205
    (coe MAlonzo.Code.Peras.QQCD.Protocol.d_defaultParams_60)
    ( coe
        MAlonzo.Code.Peras.QQCD.Types.C_MakeVerificationKey_36
        (coe MAlonzo.Code.Peras.QQCD.Crypto.d_emptyBS_8)
    )
    (coe (0 :: Integer))
    (coe (0 :: Integer))
    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
    ( coe
        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
    )
    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
    ( coe
        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
        (coe MAlonzo.Code.Peras.QQCD.Types.d_genesisCert_112)
        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
    )
    (coe MAlonzo.Code.Peras.QQCD.Types.d_genesisCert_112)
    (coe MAlonzo.Code.Peras.QQCD.Types.d_genesisCert_112)

-- Peras.QCD.Node.Model.protocol
d_protocol_52 ::
  (() -> ()) ->
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  (MAlonzo.Code.Peras.QQCD.Protocol.T_Params_26 -> AgdaAny) ->
  T_NodeModel_8 ->
  AgdaAny
d_protocol_52 ~v0 v1 = du_protocol_52 v1
du_protocol_52 ::
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  (MAlonzo.Code.Peras.QQCD.Protocol.T_Params_26 -> AgdaAny) ->
  T_NodeModel_8 ->
  AgdaAny
du_protocol_52 v0 =
  coe
    MAlonzo.Code.Peras.QQCD.State.du_lens''_206
    (coe (\v1 -> d_nodeProtocol_30 (coe v1)))
    ( coe
        ( \v1 v2 ->
            coe
              C_NodeModel'46'constructor_205
              (coe v2)
              (coe d_nodeCreatorId_32 (coe v1))
              (coe d_nodeCurrentSlot_34 (coe v1))
              (coe d_nodeCurrentRound_36 (coe v1))
              (coe d_nodePreferredChain_38 (coe v1))
              (coe d_nodeChains_40 (coe v1))
              (coe d_nodeVotes_42 (coe v1))
              (coe d_nodeCerts_44 (coe v1))
              (coe d_nodeLatestCertSeen_46 (coe v1))
              (coe d_nodeLatestCertOnChain_48 (coe v1))
        )
    )
    (coe v0)

-- Peras.QCD.Node.Model.peras
d_peras_58 ::
  MAlonzo.Code.Peras.QQCD.Protocol.T_ParamSymbol_6 ->
  MAlonzo.Code.Peras.QQCD.State.T_State_10
d_peras_58 v0 =
  coe
    MAlonzo.Code.Haskell.Prim.Functor.du__'60''36''62'__46
    ( coe
        MAlonzo.Code.Haskell.Prim.Functor.C_DefaultFunctor'46'constructor_1081
        ( \v1 v2 v3 v4 ->
            coe MAlonzo.Code.Peras.QQCD.State.du_fmapState_68 v3 v4
        )
    )
    (MAlonzo.Code.Peras.QQCD.Protocol.d_perasParam_62 (coe v0))
    ( coe
        MAlonzo.Code.Peras.QQCD.State.du_use_260
        (\v1 v2 -> coe du_protocol_52 v2)
    )

-- Peras.QCD.Node.Model.creatorId
d_creatorId_62 ::
  (() -> ()) ->
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  (MAlonzo.Code.Peras.QQCD.Types.T_VerificationKey_30 -> AgdaAny) ->
  T_NodeModel_8 ->
  AgdaAny
d_creatorId_62 ~v0 v1 = du_creatorId_62 v1
du_creatorId_62 ::
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  (MAlonzo.Code.Peras.QQCD.Types.T_VerificationKey_30 -> AgdaAny) ->
  T_NodeModel_8 ->
  AgdaAny
du_creatorId_62 v0 =
  coe
    MAlonzo.Code.Peras.QQCD.State.du_lens''_206
    (coe (\v1 -> d_nodeCreatorId_32 (coe v1)))
    ( coe
        ( \v1 v2 ->
            coe
              C_NodeModel'46'constructor_205
              (coe d_nodeProtocol_30 (coe v1))
              (coe v2)
              (coe d_nodeCurrentSlot_34 (coe v1))
              (coe d_nodeCurrentRound_36 (coe v1))
              (coe d_nodePreferredChain_38 (coe v1))
              (coe d_nodeChains_40 (coe v1))
              (coe d_nodeVotes_42 (coe v1))
              (coe d_nodeCerts_44 (coe v1))
              (coe d_nodeLatestCertSeen_46 (coe v1))
              (coe d_nodeLatestCertOnChain_48 (coe v1))
        )
    )
    (coe v0)

-- Peras.QCD.Node.Model.currentSlot
d_currentSlot_68 ::
  (() -> ()) ->
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  (Integer -> AgdaAny) ->
  T_NodeModel_8 ->
  AgdaAny
d_currentSlot_68 ~v0 v1 = du_currentSlot_68 v1
du_currentSlot_68 ::
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  (Integer -> AgdaAny) ->
  T_NodeModel_8 ->
  AgdaAny
du_currentSlot_68 v0 =
  coe
    MAlonzo.Code.Peras.QQCD.State.du_lens''_206
    (coe (\v1 -> d_nodeCurrentSlot_34 (coe v1)))
    ( coe
        ( \v1 v2 ->
            coe
              C_NodeModel'46'constructor_205
              (coe d_nodeProtocol_30 (coe v1))
              (coe d_nodeCreatorId_32 (coe v1))
              (coe v2)
              (coe d_nodeCurrentRound_36 (coe v1))
              (coe d_nodePreferredChain_38 (coe v1))
              (coe d_nodeChains_40 (coe v1))
              (coe d_nodeVotes_42 (coe v1))
              (coe d_nodeCerts_44 (coe v1))
              (coe d_nodeLatestCertSeen_46 (coe v1))
              (coe d_nodeLatestCertOnChain_48 (coe v1))
        )
    )
    (coe v0)

-- Peras.QCD.Node.Model.currentRound
d_currentRound_74 ::
  (() -> ()) ->
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  (Integer -> AgdaAny) ->
  T_NodeModel_8 ->
  AgdaAny
d_currentRound_74 ~v0 v1 = du_currentRound_74 v1
du_currentRound_74 ::
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  (Integer -> AgdaAny) ->
  T_NodeModel_8 ->
  AgdaAny
du_currentRound_74 v0 =
  coe
    MAlonzo.Code.Peras.QQCD.State.du_lens''_206
    (coe (\v1 -> d_nodeCurrentRound_36 (coe v1)))
    ( coe
        ( \v1 v2 ->
            coe
              C_NodeModel'46'constructor_205
              (coe d_nodeProtocol_30 (coe v1))
              (coe d_nodeCreatorId_32 (coe v1))
              (coe d_nodeCurrentSlot_34 (coe v1))
              (coe v2)
              (coe d_nodePreferredChain_38 (coe v1))
              (coe d_nodeChains_40 (coe v1))
              (coe d_nodeVotes_42 (coe v1))
              (coe d_nodeCerts_44 (coe v1))
              (coe d_nodeLatestCertSeen_46 (coe v1))
              (coe d_nodeLatestCertOnChain_48 (coe v1))
        )
    )
    (coe v0)

-- Peras.QCD.Node.Model.preferredChain
d_preferredChain_80 ::
  (() -> ()) ->
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  ([MAlonzo.Code.Peras.QQCD.Types.T_Block_50] -> AgdaAny) ->
  T_NodeModel_8 ->
  AgdaAny
d_preferredChain_80 ~v0 v1 = du_preferredChain_80 v1
du_preferredChain_80 ::
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  ([MAlonzo.Code.Peras.QQCD.Types.T_Block_50] -> AgdaAny) ->
  T_NodeModel_8 ->
  AgdaAny
du_preferredChain_80 v0 =
  coe
    MAlonzo.Code.Peras.QQCD.State.du_lens''_206
    (coe (\v1 -> d_nodePreferredChain_38 (coe v1)))
    ( coe
        ( \v1 v2 ->
            coe
              C_NodeModel'46'constructor_205
              (coe d_nodeProtocol_30 (coe v1))
              (coe d_nodeCreatorId_32 (coe v1))
              (coe d_nodeCurrentSlot_34 (coe v1))
              (coe d_nodeCurrentRound_36 (coe v1))
              (coe v2)
              (coe d_nodeChains_40 (coe v1))
              (coe d_nodeVotes_42 (coe v1))
              (coe d_nodeCerts_44 (coe v1))
              (coe d_nodeLatestCertSeen_46 (coe v1))
              (coe d_nodeLatestCertOnChain_48 (coe v1))
        )
    )
    (coe v0)

-- Peras.QCD.Node.Model.chains
d_chains_86 ::
  (() -> ()) ->
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  ([[MAlonzo.Code.Peras.QQCD.Types.T_Block_50]] -> AgdaAny) ->
  T_NodeModel_8 ->
  AgdaAny
d_chains_86 ~v0 v1 = du_chains_86 v1
du_chains_86 ::
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  ([[MAlonzo.Code.Peras.QQCD.Types.T_Block_50]] -> AgdaAny) ->
  T_NodeModel_8 ->
  AgdaAny
du_chains_86 v0 =
  coe
    MAlonzo.Code.Peras.QQCD.State.du_lens''_206
    (coe (\v1 -> d_nodeChains_40 (coe v1)))
    ( coe
        ( \v1 v2 ->
            coe
              C_NodeModel'46'constructor_205
              (coe d_nodeProtocol_30 (coe v1))
              (coe d_nodeCreatorId_32 (coe v1))
              (coe d_nodeCurrentSlot_34 (coe v1))
              (coe d_nodeCurrentRound_36 (coe v1))
              (coe d_nodePreferredChain_38 (coe v1))
              (coe v2)
              (coe d_nodeVotes_42 (coe v1))
              (coe d_nodeCerts_44 (coe v1))
              (coe d_nodeLatestCertSeen_46 (coe v1))
              (coe d_nodeLatestCertOnChain_48 (coe v1))
        )
    )
    (coe v0)

-- Peras.QCD.Node.Model.votes
d_votes_92 ::
  (() -> ()) ->
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  ([MAlonzo.Code.Peras.QQCD.Types.T_Vote_126] -> AgdaAny) ->
  T_NodeModel_8 ->
  AgdaAny
d_votes_92 ~v0 v1 = du_votes_92 v1
du_votes_92 ::
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  ([MAlonzo.Code.Peras.QQCD.Types.T_Vote_126] -> AgdaAny) ->
  T_NodeModel_8 ->
  AgdaAny
du_votes_92 v0 =
  coe
    MAlonzo.Code.Peras.QQCD.State.du_lens''_206
    (coe (\v1 -> d_nodeVotes_42 (coe v1)))
    ( coe
        ( \v1 v2 ->
            coe
              C_NodeModel'46'constructor_205
              (coe d_nodeProtocol_30 (coe v1))
              (coe d_nodeCreatorId_32 (coe v1))
              (coe d_nodeCurrentSlot_34 (coe v1))
              (coe d_nodeCurrentRound_36 (coe v1))
              (coe d_nodePreferredChain_38 (coe v1))
              (coe d_nodeChains_40 (coe v1))
              (coe v2)
              (coe d_nodeCerts_44 (coe v1))
              (coe d_nodeLatestCertSeen_46 (coe v1))
              (coe d_nodeLatestCertOnChain_48 (coe v1))
        )
    )
    (coe v0)

-- Peras.QCD.Node.Model.certs
d_certs_98 ::
  (() -> ()) ->
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  ([MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46] -> AgdaAny) ->
  T_NodeModel_8 ->
  AgdaAny
d_certs_98 ~v0 v1 = du_certs_98 v1
du_certs_98 ::
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  ([MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46] -> AgdaAny) ->
  T_NodeModel_8 ->
  AgdaAny
du_certs_98 v0 =
  coe
    MAlonzo.Code.Peras.QQCD.State.du_lens''_206
    (coe (\v1 -> d_nodeCerts_44 (coe v1)))
    ( coe
        ( \v1 v2 ->
            coe
              C_NodeModel'46'constructor_205
              (coe d_nodeProtocol_30 (coe v1))
              (coe d_nodeCreatorId_32 (coe v1))
              (coe d_nodeCurrentSlot_34 (coe v1))
              (coe d_nodeCurrentRound_36 (coe v1))
              (coe d_nodePreferredChain_38 (coe v1))
              (coe d_nodeChains_40 (coe v1))
              (coe d_nodeVotes_42 (coe v1))
              (coe v2)
              (coe d_nodeLatestCertSeen_46 (coe v1))
              (coe d_nodeLatestCertOnChain_48 (coe v1))
        )
    )
    (coe v0)

-- Peras.QCD.Node.Model.latestCertSeen
d_latestCertSeen_104 ::
  (() -> ()) ->
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  (MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46 -> AgdaAny) ->
  T_NodeModel_8 ->
  AgdaAny
d_latestCertSeen_104 ~v0 v1 = du_latestCertSeen_104 v1
du_latestCertSeen_104 ::
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  (MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46 -> AgdaAny) ->
  T_NodeModel_8 ->
  AgdaAny
du_latestCertSeen_104 v0 =
  coe
    MAlonzo.Code.Peras.QQCD.State.du_lens''_206
    (coe (\v1 -> d_nodeLatestCertSeen_46 (coe v1)))
    ( coe
        ( \v1 v2 ->
            coe
              C_NodeModel'46'constructor_205
              (coe d_nodeProtocol_30 (coe v1))
              (coe d_nodeCreatorId_32 (coe v1))
              (coe d_nodeCurrentSlot_34 (coe v1))
              (coe d_nodeCurrentRound_36 (coe v1))
              (coe d_nodePreferredChain_38 (coe v1))
              (coe d_nodeChains_40 (coe v1))
              (coe d_nodeVotes_42 (coe v1))
              (coe d_nodeCerts_44 (coe v1))
              (coe v2)
              (coe d_nodeLatestCertOnChain_48 (coe v1))
        )
    )
    (coe v0)

-- Peras.QCD.Node.Model.latestCertOnChain
d_latestCertOnChain_110 ::
  (() -> ()) ->
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  (MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46 -> AgdaAny) ->
  T_NodeModel_8 ->
  AgdaAny
d_latestCertOnChain_110 ~v0 v1 = du_latestCertOnChain_110 v1
du_latestCertOnChain_110 ::
  MAlonzo.Code.Haskell.Prim.Functor.T_Functor_8 ->
  (MAlonzo.Code.Peras.QQCD.Types.T_Certificate_46 -> AgdaAny) ->
  T_NodeModel_8 ->
  AgdaAny
du_latestCertOnChain_110 v0 =
  coe
    MAlonzo.Code.Peras.QQCD.State.du_lens''_206
    (coe (\v1 -> d_nodeLatestCertOnChain_48 (coe v1)))
    ( coe
        ( \v1 v2 ->
            coe
              C_NodeModel'46'constructor_205
              (coe d_nodeProtocol_30 (coe v1))
              (coe d_nodeCreatorId_32 (coe v1))
              (coe d_nodeCurrentSlot_34 (coe v1))
              (coe d_nodeCurrentRound_36 (coe v1))
              (coe d_nodePreferredChain_38 (coe v1))
              (coe d_nodeChains_40 (coe v1))
              (coe d_nodeVotes_42 (coe v1))
              (coe d_nodeCerts_44 (coe v1))
              (coe d_nodeLatestCertSeen_46 (coe v1))
              (coe v2)
        )
    )
    (coe v0)

-- Peras.QCD.Node.Model.NodeState
d_NodeState_116 :: () -> ()
d_NodeState_116 = erased

-- Peras.QCD.Node.Model.NodeOperation
d_NodeOperation_120 :: ()
d_NodeOperation_120 = erased

-- Peras.QCD.Node.Model.NodeModification
d_NodeModification_122 :: ()
d_NodeModification_122 = erased

-- Peras.QCD.Node.Model.diffuse
d_diffuse_124 :: MAlonzo.Code.Peras.QQCD.State.T_State_10
d_diffuse_124 =
  coe
    MAlonzo.Code.Peras.QQCD.State.du_pureState_82
    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
