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

module MAlonzo.Code.Peras.SmallStep where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Extrema
import qualified MAlonzo.Code.Data.List.Membership.Propositional.Properties
import qualified MAlonzo.Code.Data.List.Relation.Binary.Subset.Propositional.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Tree.AVL
import qualified MAlonzo.Code.Data.Tree.AVL.Map
import qualified MAlonzo.Code.Peras.Block
import qualified MAlonzo.Code.Peras.Chain
import qualified MAlonzo.Code.Peras.Crypto
import qualified MAlonzo.Code.Peras.Numbering
import qualified MAlonzo.Code.Peras.Params
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
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

-- Peras.SmallStep._.argmax
d_argmax_6 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny
d_argmax_6 v0 v1 v2 =
  coe
    MAlonzo.Code.Data.List.Extrema.du_argmax_136
    (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2696)
    v2

-- Peras.SmallStep.M.Map
d_Map_12 :: MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()
d_Map_12 = erased

-- Peras.SmallStep.M.insert
d_insert_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_insert_26 v0 v1 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
    (coe MAlonzo.Code.Peras.Block.d_PartyIdO_6)

-- Peras.SmallStep.M.lookup
d_lookup_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  Integer ->
  Maybe AgdaAny
d_lookup_38 v0 v1 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Map.du_lookup_208
    (coe MAlonzo.Code.Peras.Block.d_PartyIdO_6)

-- Peras.SmallStep._._⊆_
d__'8838'__60 ::
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  ()
d__'8838'__60 = erased

-- Peras.SmallStep.Message
d_Message_62 = ()
data T_Message_62
  = C_BlockMsg_64 MAlonzo.Code.Peras.Block.T_Block_62
  | C_VoteMsg_66 MAlonzo.Code.Peras.Chain.T_Vote_4

-- Peras.SmallStep.Message-injective
d_Message'45'injective_72 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Message'45'injective_72 = erased

-- Peras.SmallStep.Message-injective′
d_Message'45'injective'8242'_78 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  ( MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
  ) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_Message'45'injective'8242'_78 = erased

-- Peras.SmallStep.Delay
d_Delay_80 :: ()
d_Delay_80 = erased

-- Peras.SmallStep.Envelope
d_Envelope_82 = ()
data T_Envelope_82
  = C_'10629'_'44'_'44'_'44'_'10630'_100
      Integer
      MAlonzo.Code.Peras.Block.T_Honesty_26
      T_Message_62
      MAlonzo.Code.Data.Fin.Base.T_Fin_10

-- Peras.SmallStep.Envelope.partyId
d_partyId_92 :: T_Envelope_82 -> Integer
d_partyId_92 v0 =
  case coe v0 of
    C_'10629'_'44'_'44'_'44'_'10630'_100 v1 v2 v3 v4 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep.Envelope.honesty
d_honesty_94 ::
  T_Envelope_82 -> MAlonzo.Code.Peras.Block.T_Honesty_26
d_honesty_94 v0 =
  case coe v0 of
    C_'10629'_'44'_'44'_'44'_'10630'_100 v1 v2 v3 v4 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep.Envelope.message
d_message_96 :: T_Envelope_82 -> T_Message_62
d_message_96 v0 =
  case coe v0 of
    C_'10629'_'44'_'44'_'44'_'10630'_100 v1 v2 v3 v4 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep.Envelope.delay
d_delay_98 :: T_Envelope_82 -> MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_delay_98 v0 =
  case coe v0 of
    C_'10629'_'44'_'44'_'44'_'10630'_100 v1 v2 v3 v4 -> coe v4
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep.⦅⦆-injective
d_'10629''10630''45'injective_106 ::
  T_Envelope_82 ->
  T_Envelope_82 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10629''10630''45'injective_106 = erased

-- Peras.SmallStep.⦅⦆-injective₃
d_'10629''10630''45'injective'8323'_112 ::
  T_Envelope_82 ->
  T_Envelope_82 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10629''10630''45'injective'8323'_112 = erased

-- Peras.SmallStep.⦅⦆-injective′
d_'10629''10630''45'injective'8242'_118 ::
  T_Envelope_82 ->
  T_Envelope_82 ->
  ( MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
  ) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'10629''10630''45'injective'8242'_118 = erased

-- Peras.SmallStep.⦅⦆-injective₃′
d_'10629''10630''45'injective'8323''8242'_124 ::
  T_Envelope_82 ->
  T_Envelope_82 ->
  ( MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
  ) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'10629''10630''45'injective'8323''8242'_124 = erased

-- Peras.SmallStep._≐_
d__'8784'__126 ::
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  ()
d__'8784'__126 = erased

-- Peras.SmallStep._.getCert
d_getCert_178 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
  [MAlonzo.Code.Peras.Block.T_Certificate_66] ->
  Maybe MAlonzo.Code.Peras.Block.T_Certificate_66
d_getCert_178 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 =
  du_getCert_178 v9 v10
du_getCert_178 ::
  MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
  [MAlonzo.Code.Peras.Block.T_Certificate_66] ->
  Maybe MAlonzo.Code.Peras.Block.T_Certificate_66
du_getCert_178 v0 v1 =
  coe
    MAlonzo.Code.Data.List.Base.du_head_608
    ( coe
        MAlonzo.Code.Data.List.Base.du_filter_740
        ( coe
            ( \v2 ->
                MAlonzo.Code.Peras.Numbering.d__'8799''45'RoundNumber__40
                  (coe MAlonzo.Code.Peras.Block.d_round_72 (coe v2))
                  (coe v0)
            )
        )
        (coe v1)
    )

-- Peras.SmallStep._.latestCert
d_latestCert_184 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  [MAlonzo.Code.Peras.Block.T_Certificate_66] ->
  MAlonzo.Code.Peras.Block.T_Certificate_66
d_latestCert_184 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 =
  du_latestCert_184 v1
du_latestCert_184 ::
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  [MAlonzo.Code.Peras.Block.T_Certificate_66] ->
  MAlonzo.Code.Peras.Block.T_Certificate_66
du_latestCert_184 v0 =
  coe
    MAlonzo.Code.Data.List.Extrema.du_argmax_136
    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2696
    MAlonzo.Code.Peras.Block.d_roundNumber_76
    v0

-- Peras.SmallStep._.IsTreeType
d_IsTreeType_202
  a0
  a1
  a2
  a3
  a4
  a5
  a6
  a7
  a8
  a9
  a10
  a11
  a12
  a13
  a14
  a15
  a16 =
    ()
data T_IsTreeType_202
  = C_IsTreeType'46'constructor_15529
      ( AgdaAny ->
        MAlonzo.Code.Peras.Block.T_Block_62 ->
        MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
      )
      ( AgdaAny ->
        MAlonzo.Code.Peras.Chain.T_Vote_4 ->
        MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
      )
      ( AgdaAny ->
        MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
        MAlonzo.Code.Peras.Chain.T_ValidChain_158
      )
      ( [MAlonzo.Code.Peras.Block.T_Block_62] ->
        AgdaAny ->
        MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
        MAlonzo.Code.Peras.Chain.T_ValidChain_158 ->
        ( MAlonzo.Code.Peras.Block.T_Block_62 ->
          MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
          MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
        ) ->
        MAlonzo.Code.Data.Nat.Base.T__'8804'__22
      )
      ( AgdaAny ->
        MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
        MAlonzo.Code.Peras.Block.T_Block_62 ->
        MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
        MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
      )
      ( AgdaAny ->
        MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
      )

-- Peras.SmallStep._.IsTreeType.allBlocksUpTo
d_allBlocksUpTo_310 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Peras.Block.T_Block_62 -> AgdaAny) ->
  (AgdaAny -> [MAlonzo.Code.Peras.Block.T_Block_62]) ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    AgdaAny ->
    [MAlonzo.Code.Peras.Block.T_Block_62]
  ) ->
  (AgdaAny -> MAlonzo.Code.Peras.Chain.T_Vote_4 -> AgdaAny) ->
  (AgdaAny -> [MAlonzo.Code.Peras.Chain.T_Vote_4]) ->
  (AgdaAny -> [MAlonzo.Code.Peras.Block.T_Certificate_66]) ->
  T_IsTreeType_202 ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
  AgdaAny ->
  [MAlonzo.Code.Peras.Block.T_Block_62]
d_allBlocksUpTo_310
  ~v0
  ~v1
  ~v2
  ~v3
  ~v4
  ~v5
  ~v6
  ~v7
  ~v8
  ~v9
  ~v10
  ~v11
  v12
  ~v13
  ~v14
  ~v15
  ~v16
  ~v17
  v18
  v19 =
    du_allBlocksUpTo_310 v12 v18 v19
du_allBlocksUpTo_310 ::
  (AgdaAny -> [MAlonzo.Code.Peras.Block.T_Block_62]) ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
  AgdaAny ->
  [MAlonzo.Code.Peras.Block.T_Block_62]
du_allBlocksUpTo_310 v0 v1 v2 =
  coe
    MAlonzo.Code.Data.List.Base.du_filter_740
    ( coe
        ( \v3 ->
            MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2672
              (coe MAlonzo.Code.Peras.Block.d_slotNumber''_108 (coe v3))
              (coe MAlonzo.Code.Peras.Numbering.d_getSlotNumber_8 (coe v1))
        )
    )
    (coe v0 v2)

-- Peras.SmallStep._.IsTreeType.instantiated
d_instantiated_318 ::
  T_IsTreeType_202 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_instantiated_318 = erased

-- Peras.SmallStep._.IsTreeType.instantiated-certs
d_instantiated'45'certs_320 ::
  T_IsTreeType_202 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_instantiated'45'certs_320 = erased

-- Peras.SmallStep._.IsTreeType.extendable
d_extendable_326 ::
  T_IsTreeType_202 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extendable_326 v0 =
  case coe v0 of
    C_IsTreeType'46'constructor_15529 v3 v5 v6 v7 v8 v9 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.IsTreeType.extendable-certs
d_extendable'45'certs_332 ::
  T_IsTreeType_202 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extendable'45'certs_332 = erased

-- Peras.SmallStep._.IsTreeType.extendable-votes
d_extendable'45'votes_338 ::
  T_IsTreeType_202 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Chain.T_Vote_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extendable'45'votes_338 v0 =
  case coe v0 of
    C_IsTreeType'46'constructor_15529 v3 v5 v6 v7 v8 v9 -> coe v5
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.IsTreeType.valid
d_valid_344 ::
  T_IsTreeType_202 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
  MAlonzo.Code.Peras.Chain.T_ValidChain_158
d_valid_344 v0 =
  case coe v0 of
    C_IsTreeType'46'constructor_15529 v3 v5 v6 v7 v8 v9 -> coe v6
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.IsTreeType.optimal
d_optimal_356 ::
  T_IsTreeType_202 ->
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  AgdaAny ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
  MAlonzo.Code.Peras.Chain.T_ValidChain_158 ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
  ) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_optimal_356 v0 =
  case coe v0 of
    C_IsTreeType'46'constructor_15529 v3 v5 v6 v7 v8 v9 -> coe v7
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.IsTreeType.self-contained
d_self'45'contained_362 ::
  T_IsTreeType_202 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_self'45'contained_362 v0 =
  case coe v0 of
    C_IsTreeType'46'constructor_15529 v3 v5 v6 v7 v8 v9 -> coe v8
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.IsTreeType.valid-votes
d_valid'45'votes_366 ::
  T_IsTreeType_202 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_valid'45'votes_366 v0 =
  case coe v0 of
    C_IsTreeType'46'constructor_15529 v3 v5 v6 v7 v8 v9 -> coe v9
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.IsTreeType.unique-votes
d_unique'45'votes_374 ::
  T_IsTreeType_202 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Chain.T_Vote_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'45'votes_374 = erased

-- Peras.SmallStep._.IsTreeType.no-equivocations
d_no'45'equivocations_384 ::
  T_IsTreeType_202 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Chain.T_Vote_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'equivocations_384 = erased

-- Peras.SmallStep._.IsTreeType.non-quorum
d_non'45'quorum_390 ::
  T_IsTreeType_202 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_non'45'quorum_390 = erased

-- Peras.SmallStep._.IsTreeType.quorum
d_quorum_398 ::
  T_IsTreeType_202 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_quorum_398 = erased

-- Peras.SmallStep._.TreeType
d_TreeType_402 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_TreeType_402
  = C_TreeType'46'constructor_20203
      AgdaAny
      (AgdaAny -> MAlonzo.Code.Peras.Block.T_Block_62 -> AgdaAny)
      (AgdaAny -> [MAlonzo.Code.Peras.Block.T_Block_62])
      ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
        AgdaAny ->
        [MAlonzo.Code.Peras.Block.T_Block_62]
      )
      (AgdaAny -> MAlonzo.Code.Peras.Chain.T_Vote_4 -> AgdaAny)
      (AgdaAny -> [MAlonzo.Code.Peras.Chain.T_Vote_4])
      (AgdaAny -> [MAlonzo.Code.Peras.Block.T_Certificate_66])
      T_IsTreeType_202

-- Peras.SmallStep._.TreeType.tree₀
d_tree'8320'_422 :: T_TreeType_402 -> AgdaAny
d_tree'8320'_422 v0 =
  case coe v0 of
    C_TreeType'46'constructor_20203 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.TreeType.extendTree
d_extendTree_424 ::
  T_TreeType_402 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  AgdaAny
d_extendTree_424 v0 =
  case coe v0 of
    C_TreeType'46'constructor_20203 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.TreeType.allBlocks
d_allBlocks_426 ::
  T_TreeType_402 -> AgdaAny -> [MAlonzo.Code.Peras.Block.T_Block_62]
d_allBlocks_426 v0 =
  case coe v0 of
    C_TreeType'46'constructor_20203 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.TreeType.bestChain
d_bestChain_428 ::
  T_TreeType_402 ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
  AgdaAny ->
  [MAlonzo.Code.Peras.Block.T_Block_62]
d_bestChain_428 v0 =
  case coe v0 of
    C_TreeType'46'constructor_20203 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v4
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.TreeType.addVote
d_addVote_430 ::
  T_TreeType_402 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Chain.T_Vote_4 ->
  AgdaAny
d_addVote_430 v0 =
  case coe v0 of
    C_TreeType'46'constructor_20203 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v5
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.TreeType.votes
d_votes_432 ::
  T_TreeType_402 -> AgdaAny -> [MAlonzo.Code.Peras.Chain.T_Vote_4]
d_votes_432 v0 =
  case coe v0 of
    C_TreeType'46'constructor_20203 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v6
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.TreeType.certs
d_certs_434 ::
  T_TreeType_402 ->
  AgdaAny ->
  [MAlonzo.Code.Peras.Block.T_Certificate_66]
d_certs_434 v0 =
  case coe v0 of
    C_TreeType'46'constructor_20203 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v7
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.TreeType.is-TreeType
d_is'45'TreeType_436 :: T_TreeType_402 -> T_IsTreeType_202
d_is'45'TreeType_436 v0 =
  case coe v0 of
    C_TreeType'46'constructor_20203 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v8
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.TreeType.tipBest
d_tipBest_438 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_402 ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Block.T_Block_62
d_tipBest_438 v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10 v11 v12 =
  du_tipBest_438 v0 v6 v10 v11 v12
du_tipBest_438 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  T_TreeType_402 ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Block.T_Block_62
du_tipBest_438 v0 v1 v2 v3 v4 =
  coe
    MAlonzo.Code.Peras.Chain.du_tip_172
    (coe v0)
    (coe v1)
    (coe d_bestChain_428 v2 v3 v4)
    (coe d_valid_344 (d_is'45'TreeType_436 (coe v2)) v4 v3)

-- Peras.SmallStep._.TreeType.latestCertOnChain
d_latestCertOnChain_448 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_402 ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Block.T_Certificate_66
d_latestCertOnChain_448
  ~v0
  v1
  ~v2
  ~v3
  ~v4
  ~v5
  ~v6
  ~v7
  ~v8
  ~v9
  v10
  v11
  v12 =
    du_latestCertOnChain_448 v1 v10 v11 v12
du_latestCertOnChain_448 ::
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  T_TreeType_402 ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Block.T_Certificate_66
du_latestCertOnChain_448 v0 v1 v2 v3 =
  coe
    du_latestCert_184
    v0
    ( coe
        MAlonzo.Code.Data.List.Base.du_catMaybes_60
        ( coe
            MAlonzo.Code.Data.List.Base.du_map_22
            (coe (\v4 -> MAlonzo.Code.Peras.Block.d_certificate_100 (coe v4)))
            (coe d_bestChain_428 v1 v2 v3)
        )
    )

-- Peras.SmallStep._.TreeType.latestCertSeen
d_latestCertSeen_452 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_402 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Block.T_Certificate_66
d_latestCertSeen_452 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11 =
  du_latestCertSeen_452 v1 v10 v11
du_latestCertSeen_452 ::
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  T_TreeType_402 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Block.T_Certificate_66
du_latestCertSeen_452 v0 v1 v2 =
  coe du_latestCert_184 v0 (coe d_certs_434 v1 v2)

-- Peras.SmallStep._.LocalState
d_LocalState_458 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
newtype T_LocalState_458 = C_'10218'_'10219'_468 AgdaAny

-- Peras.SmallStep._.LocalState.tree
d_tree_466 :: T_LocalState_458 -> AgdaAny
d_tree_466 v0 =
  case coe v0 of
    C_'10218'_'10219'_468 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.⟪⟫-injective
d_'10218''10219''45'injective_478 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_402 ->
  T_LocalState_458 ->
  T_LocalState_458 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10218''10219''45'injective_478 = erased

-- Peras.SmallStep._._.Stateˡ
d_State'737'_496 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  ()
d_State'737'_496 = erased

-- Peras.SmallStep._._._[_]→_
d__'91'_'93''8594'__498
  a0
  a1
  a2
  a3
  a4
  a5
  a6
  a7
  a8
  a9
  a10
  a11
  a12
  a13
  a14
  a15
  a16
  a17 =
    ()
data T__'91'_'93''8594'__498
  = C_VoteReceived_504
  | C_BlockReceived_510

-- Peras.SmallStep._._.VoteInRound
d_VoteInRound_512
  a0
  a1
  a2
  a3
  a4
  a5
  a6
  a7
  a8
  a9
  a10
  a11
  a12
  a13
  a14
  a15
  a16 =
    ()
data T_VoteInRound_512
  = C_Regular_522 MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
  | C_AfterCooldown_534
      Integer
      MAlonzo.Code.Data.Nat.Base.T__'8804'__22
      MAlonzo.Code.Data.Nat.Base.T__'8804'__22

-- Peras.SmallStep._._.Stateᵍ
d_State'7501'_536 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 =
  ()
data T_State'7501'_536
  = C_'10214'_'44'_'44'_'44'_'44'_'10215'_558
      MAlonzo.Code.Peras.Numbering.T_SlotNumber_4
      MAlonzo.Code.Data.Tree.AVL.T_Tree_254
      [T_Envelope_82]
      [T_Message_62]
      AgdaAny

-- Peras.SmallStep._._.Stateᵍ.clock
d_clock_548 ::
  T_State'7501'_536 -> MAlonzo.Code.Peras.Numbering.T_SlotNumber_4
d_clock_548 v0 =
  case coe v0 of
    C_'10214'_'44'_'44'_'44'_'44'_'10215'_558 v1 v2 v3 v4 v5 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._._.Stateᵍ.stateMap
d_stateMap_550 ::
  T_State'7501'_536 -> MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_stateMap_550 v0 =
  case coe v0 of
    C_'10214'_'44'_'44'_'44'_'44'_'10215'_558 v1 v2 v3 v4 v5 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._._.Stateᵍ.messages
d_messages_552 :: T_State'7501'_536 -> [T_Envelope_82]
d_messages_552 v0 =
  case coe v0 of
    C_'10214'_'44'_'44'_'44'_'44'_'10215'_558 v1 v2 v3 v4 v5 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._._.Stateᵍ.history
d_history_554 :: T_State'7501'_536 -> [T_Message_62]
d_history_554 v0 =
  case coe v0 of
    C_'10214'_'44'_'44'_'44'_'44'_'10215'_558 v1 v2 v3 v4 v5 -> coe v4
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._._.Stateᵍ.adversarialState
d_adversarialState_556 :: T_State'7501'_536 -> AgdaAny
d_adversarialState_556 v0 =
  case coe v0 of
    C_'10214'_'44'_'44'_'44'_'44'_'10215'_558 v1 v2 v3 v4 v5 -> coe v5
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._._.Delivered
d_Delivered_560 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_536 ->
  ()
d_Delivered_560 = erased

-- Peras.SmallStep._._._,_,_,_↑_
d__'44'_'44'_'44'_'8593'__570 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_Message_62 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  Integer ->
  T_LocalState_458 ->
  T_State'7501'_536 ->
  T_State'7501'_536
d__'44'_'44'_'44'_'8593'__570
  ~v0
  ~v1
  ~v2
  ~v3
  ~v4
  ~v5
  ~v6
  ~v7
  ~v8
  ~v9
  ~v10
  ~v11
  ~v12
  ~v13
  v14
  v15
  v16
  v17
  v18
  v19 =
    du__'44'_'44'_'44'_'8593'__570 v14 v15 v16 v17 v18 v19
du__'44'_'44'_'44'_'8593'__570 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_Message_62 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  Integer ->
  T_LocalState_458 ->
  T_State'7501'_536 ->
  T_State'7501'_536
du__'44'_'44'_'44'_'8593'__570 v0 v1 v2 v3 v4 v5 =
  case coe v5 of
    C_'10214'_'44'_'44'_'44'_'44'_'10215'_558 v6 v7 v8 v9 v10 ->
      coe
        C_'10214'_'44'_'44'_'44'_'44'_'10215'_558
        (coe v6)
        ( coe
            MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
            MAlonzo.Code.Peras.Block.d_PartyIdO_6
            v3
            v4
            v7
        )
        ( coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__62
            ( coe
                MAlonzo.Code.Data.List.Base.du_map_22
                ( coe
                    MAlonzo.Code.Data.Product.Base.du_uncurry_244
                    ( coe
                        ( \v11 v12 ->
                            coe
                              C_'10629'_'44'_'44'_'44'_'10630'_100
                              (coe v11)
                              (coe v12)
                              (coe v1)
                              (coe v2)
                        )
                    )
                )
                ( coe
                    MAlonzo.Code.Data.List.Base.du_filter_740
                    ( coe
                        ( \v11 ->
                            coe
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_68
                              ( coe
                                  MAlonzo.Code.Data.Nat.Properties.d__'8799'__2558
                                  (coe v3)
                                  (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v11))
                              )
                        )
                    )
                    (coe v0)
                )
            )
            (coe v8)
        )
        ( coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe v1)
            (coe v9)
        )
        (coe v10)
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._._.tick
d_tick_596 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_536 ->
  T_State'7501'_536
d_tick_596
  ~v0
  ~v1
  ~v2
  ~v3
  ~v4
  ~v5
  ~v6
  ~v7
  ~v8
  ~v9
  ~v10
  ~v11
  ~v12
  ~v13
  ~v14
  v15 =
    du_tick_596 v15
du_tick_596 :: T_State'7501'_536 -> T_State'7501'_536
du_tick_596 v0 =
  coe
    C_'10214'_'44'_'44'_'44'_'44'_'10215'_558
    ( coe
        MAlonzo.Code.Peras.Numbering.d_next_10
        (coe d_clock_548 (coe v0))
    )
    (coe d_stateMap_550 (coe v0))
    ( coe
        MAlonzo.Code.Data.List.Base.du_map_22
        ( coe
            ( \v1 ->
                coe
                  C_'10629'_'44'_'44'_'44'_'10630'_100
                  (coe d_partyId_92 (coe v1))
                  (coe d_honesty_94 (coe v1))
                  (coe d_message_96 (coe v1))
                  ( coe
                      MAlonzo.Code.Data.Fin.Base.du_pred_384
                      (coe d_delay_98 (coe v1))
                  )
            )
        )
        (coe d_messages_552 (coe v0))
    )
    (coe d_history_554 (coe v0))
    (coe d_adversarialState_556 (coe v0))

-- Peras.SmallStep._._._⊢_[_]⇀_
d__'8866'_'91'_'93''8640'__610
  a0
  a1
  a2
  a3
  a4
  a5
  a6
  a7
  a8
  a9
  a10
  a11
  a12
  a13
  a14
  a15
  a16
  a17
  a18
  a19 =
    ()
data T__'8866'_'91'_'93''8640'__610
  = C_honest_632
      T_LocalState_458
      T_LocalState_458
      MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
      T__'91'_'93''8594'__498
  | C_corrupt_652 MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34

-- Peras.SmallStep._._._⊢_⇉_
d__'8866'_'8649'__656
  a0
  a1
  a2
  a3
  a4
  a5
  a6
  a7
  a8
  a9
  a10
  a11
  a12
  a13
  a14
  a15
  a16
  a17
  a18 =
    ()
data T__'8866'_'8649'__656
  = C_honest_688
      AgdaAny
      MAlonzo.Code.Peras.Crypto.T_MembershipProof_42
      MAlonzo.Code.Peras.Crypto.T_Signature_70
      MAlonzo.Code.Peras.Chain.T_Vote_4
      AgdaAny
      AgdaAny
      T_VoteInRound_512

-- Peras.SmallStep._._._.adversarialState
d_adversarialState_672 ::
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_536 ->
  MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Chain.T_Vote_4 ->
  AgdaAny
d_adversarialState_672 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_adversarialState_672 v7
du_adversarialState_672 :: T_State'7501'_536 -> AgdaAny
du_adversarialState_672 v0 = coe d_adversarialState_556 (coe v0)

-- Peras.SmallStep._._._.clock
d_clock_674 ::
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_536 ->
  MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Chain.T_Vote_4 ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4
d_clock_674 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_clock_674 v7
du_clock_674 ::
  T_State'7501'_536 -> MAlonzo.Code.Peras.Numbering.T_SlotNumber_4
du_clock_674 v0 = coe d_clock_548 (coe v0)

-- Peras.SmallStep._._._.history
d_history_676 ::
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_536 ->
  MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Chain.T_Vote_4 ->
  [T_Message_62]
d_history_676 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_history_676 v7
du_history_676 :: T_State'7501'_536 -> [T_Message_62]
du_history_676 v0 = coe d_history_554 (coe v0)

-- Peras.SmallStep._._._.messages
d_messages_678 ::
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_536 ->
  MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Chain.T_Vote_4 ->
  [T_Envelope_82]
d_messages_678 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_messages_678 v7
du_messages_678 :: T_State'7501'_536 -> [T_Envelope_82]
du_messages_678 v0 = coe d_messages_552 (coe v0)

-- Peras.SmallStep._._._.stateMap
d_stateMap_680 ::
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_536 ->
  MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Chain.T_Vote_4 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_stateMap_680 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_stateMap_680 v7
du_stateMap_680 ::
  T_State'7501'_536 -> MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_stateMap_680 v0 = coe d_stateMap_550 (coe v0)

-- Peras.SmallStep._._._⊢_↷_
d__'8866'_'8631'__692
  a0
  a1
  a2
  a3
  a4
  a5
  a6
  a7
  a8
  a9
  a10
  a11
  a12
  a13
  a14
  a15
  a16
  a17
  a18 =
    ()
data T__'8866'_'8631'__692
  = C_honest_724
      AgdaAny
      MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56
      MAlonzo.Code.Peras.Crypto.T_Signature_70
      MAlonzo.Code.Peras.Block.T_Block_62
      AgdaAny
      AgdaAny
  | C_honest'45'cooldown_768
      AgdaAny
      MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56
      MAlonzo.Code.Peras.Crypto.T_Signature_70
      MAlonzo.Code.Peras.Block.T_Block_62
      AgdaAny
      AgdaAny
      MAlonzo.Code.Data.Nat.Base.T__'8804'__22
      MAlonzo.Code.Data.Nat.Base.T__'8804'__22

-- Peras.SmallStep._._._.adversarialState
d_adversarialState_708 ::
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_536 ->
  MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  AgdaAny
d_adversarialState_708 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_adversarialState_708 v7
du_adversarialState_708 :: T_State'7501'_536 -> AgdaAny
du_adversarialState_708 v0 = coe d_adversarialState_556 (coe v0)

-- Peras.SmallStep._._._.clock
d_clock_710 ::
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_536 ->
  MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4
d_clock_710 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_clock_710 v7
du_clock_710 ::
  T_State'7501'_536 -> MAlonzo.Code.Peras.Numbering.T_SlotNumber_4
du_clock_710 v0 = coe d_clock_548 (coe v0)

-- Peras.SmallStep._._._.history
d_history_712 ::
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_536 ->
  MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  [T_Message_62]
d_history_712 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_history_712 v7
du_history_712 :: T_State'7501'_536 -> [T_Message_62]
du_history_712 v0 = coe d_history_554 (coe v0)

-- Peras.SmallStep._._._.messages
d_messages_714 ::
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_536 ->
  MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  [T_Envelope_82]
d_messages_714 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_messages_714 v7
du_messages_714 :: T_State'7501'_536 -> [T_Envelope_82]
du_messages_714 v0 = coe d_messages_552 (coe v0)

-- Peras.SmallStep._._._.stateMap
d_stateMap_716 ::
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_536 ->
  MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_stateMap_716 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_stateMap_716 v7
du_stateMap_716 ::
  T_State'7501'_536 -> MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_stateMap_716 v0 = coe d_stateMap_550 (coe v0)

-- Peras.SmallStep._._._.adversarialState
d_adversarialState_740 ::
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_536 ->
  MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  AgdaAny
d_adversarialState_740 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_adversarialState_740 v7
du_adversarialState_740 :: T_State'7501'_536 -> AgdaAny
du_adversarialState_740 v0 = coe d_adversarialState_556 (coe v0)

-- Peras.SmallStep._._._.clock
d_clock_742 ::
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_536 ->
  MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4
d_clock_742 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_clock_742 v7
du_clock_742 ::
  T_State'7501'_536 -> MAlonzo.Code.Peras.Numbering.T_SlotNumber_4
du_clock_742 v0 = coe d_clock_548 (coe v0)

-- Peras.SmallStep._._._.history
d_history_744 ::
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_536 ->
  MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  [T_Message_62]
d_history_744 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_history_744 v7
du_history_744 :: T_State'7501'_536 -> [T_Message_62]
du_history_744 v0 = coe d_history_554 (coe v0)

-- Peras.SmallStep._._._.messages
d_messages_746 ::
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_536 ->
  MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  [T_Envelope_82]
d_messages_746 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_messages_746 v7
du_messages_746 :: T_State'7501'_536 -> [T_Envelope_82]
du_messages_746 v0 = coe d_messages_552 (coe v0)

-- Peras.SmallStep._._._.stateMap
d_stateMap_748 ::
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_536 ->
  MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_stateMap_748 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_stateMap_748 v7
du_stateMap_748 ::
  T_State'7501'_536 -> MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_stateMap_748 v0 = coe d_stateMap_550 (coe v0)

-- Peras.SmallStep._._._↝_
d__'8605'__780
  a0
  a1
  a2
  a3
  a4
  a5
  a6
  a7
  a8
  a9
  a10
  a11
  a12
  a13
  a14
  a15
  a16 =
    ()
data T__'8605'__780
  = C_Deliver_784
      Integer
      MAlonzo.Code.Peras.Block.T_Honesty_26
      T_Message_62
      T__'8866'_'91'_'93''8640'__610
  | C_CastVote_786
      Integer
      MAlonzo.Code.Peras.Block.T_Honesty_26
      T__'8866'_'8649'__656
  | C_CreateBlock_788
      Integer
      MAlonzo.Code.Peras.Block.T_Honesty_26
      T__'8866'_'8631'__692
  | C_NextSlot_790 MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44

-- Peras.SmallStep._._._↝⋆_
d__'8605''8902'__792
  a0
  a1
  a2
  a3
  a4
  a5
  a6
  a7
  a8
  a9
  a10
  a11
  a12
  a13
  a14
  a15
  a16 =
    ()
data T__'8605''8902'__792
  = C_'91''93''8242'_794
  | C__'8759''8242'__796
      T_State'7501'_536
      T__'8605'__780
      T__'8605''8902'__792

-- Peras.SmallStep._._.↝⋆∘↝⋆
d_'8605''8902''8728''8605''8902'_798 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_536 ->
  T_State'7501'_536 ->
  T_State'7501'_536 ->
  T__'8605''8902'__792 ->
  T__'8605''8902'__792 ->
  T__'8605''8902'__792
d_'8605''8902''8728''8605''8902'_798
  ~v0
  ~v1
  ~v2
  ~v3
  ~v4
  ~v5
  ~v6
  ~v7
  ~v8
  ~v9
  ~v10
  ~v11
  ~v12
  ~v13
  ~v14
  ~v15
  ~v16
  ~v17
  v18
  v19 =
    du_'8605''8902''8728''8605''8902'_798 v18 v19
du_'8605''8902''8728''8605''8902'_798 ::
  T__'8605''8902'__792 ->
  T__'8605''8902'__792 ->
  T__'8605''8902'__792
du_'8605''8902''8728''8605''8902'_798 v0 v1 =
  case coe v0 of
    C_'91''93''8242'_794 -> coe v1
    C__'8759''8242'__796 v3 v5 v6 ->
      coe
        C__'8759''8242'__796
        v3
        v5
        (coe du_'8605''8902''8728''8605''8902'_798 (coe v6) (coe v1))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._._.↝∘↝⋆
d_'8605''8728''8605''8902'_808 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_536 ->
  T_State'7501'_536 ->
  T_State'7501'_536 ->
  T__'8605''8902'__792 ->
  T__'8605'__780 ->
  T__'8605''8902'__792
d_'8605''8728''8605''8902'_808
  ~v0
  ~v1
  ~v2
  ~v3
  ~v4
  ~v5
  ~v6
  ~v7
  ~v8
  ~v9
  ~v10
  ~v11
  ~v12
  ~v13
  ~v14
  ~v15
  ~v16
  v17
  v18
  v19 =
    du_'8605''8728''8605''8902'_808 v17 v18 v19
du_'8605''8728''8605''8902'_808 ::
  T_State'7501'_536 ->
  T__'8605''8902'__792 ->
  T__'8605'__780 ->
  T__'8605''8902'__792
du_'8605''8728''8605''8902'_808 v0 v1 v2 =
  case coe v1 of
    C_'91''93''8242'_794 ->
      coe C__'8759''8242'__796 v0 v2 (coe C_'91''93''8242'_794)
    C__'8759''8242'__796 v4 v6 v7 ->
      coe
        C__'8759''8242'__796
        v4
        v6
        (coe du_'8605''8728''8605''8902'_808 (coe v0) (coe v7) (coe v2))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._._.CollisionFree
d_CollisionFree_820
  a0
  a1
  a2
  a3
  a4
  a5
  a6
  a7
  a8
  a9
  a10
  a11
  a12
  a13
  a14
  a15 =
    ()
data T_CollisionFree_820
  = C_collision'45'free_834
      MAlonzo.Code.Peras.Block.T_Block_62
      MAlonzo.Code.Peras.Block.T_Block_62
      MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44

-- Peras.SmallStep._._._._⊆_
d__'8838'__838 ::
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [T_Message_62] ->
  [T_Message_62] ->
  ()
d__'8838'__838 = erased

-- Peras.SmallStep._._._._⊇_
d__'8839'__840 ::
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [T_Message_62] ->
  [T_Message_62] ->
  ()
d__'8839'__840 = erased

-- Peras.SmallStep._._._._⊆_
d__'8838'__844 ::
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  ()
d__'8838'__844 = erased

-- Peras.SmallStep._._.⊆→⊆-cartesianProduct
d_'8838''8594''8838''45'cartesianProduct_856 ::
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [T_Message_62] ->
  [T_Message_62] ->
  ( T_Message_62 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
  ) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_'8838''8594''8838''45'cartesianProduct_856
  ~v0
  ~v1
  ~v2
  ~v3
  ~v4
  v5
  v6
  v7
  v8
  v9 =
    du_'8838''8594''8838''45'cartesianProduct_856 v5 v6 v7 v8 v9
du_'8838''8594''8838''45'cartesianProduct_856 ::
  [T_Message_62] ->
  [T_Message_62] ->
  ( T_Message_62 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
  ) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_'8838''8594''8838''45'cartesianProduct_856 v0 v1 v2 v3 v4 =
  coe
    MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45'cartesianProduct'8314'_360
    (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
    (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
    v1
    v1
    ( coe
        v2
        (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
        ( MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            ( coe
                MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45'cartesianProduct'8315'_372
                (coe v0)
                (coe v0)
                (coe v3)
                (coe v4)
            )
        )
    )
    ( coe
        v2
        (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
        ( MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            ( coe
                MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45'cartesianProduct'8315'_372
                (coe v0)
                (coe v0)
                (coe v3)
                (coe v4)
            )
        )
    )

-- Peras.SmallStep._._.collision-free-resp-⊇
d_collision'45'free'45'resp'45''8839'_872 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_536 ->
  T_State'7501'_536 ->
  T_CollisionFree_820 ->
  ( T_Message_62 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
  ) ->
  T_CollisionFree_820
d_collision'45'free'45'resp'45''8839'_872
  ~v0
  ~v1
  ~v2
  ~v3
  ~v4
  ~v5
  ~v6
  ~v7
  ~v8
  ~v9
  ~v10
  ~v11
  ~v12
  ~v13
  ~v14
  v15
  v16
  v17
  v18 =
    du_collision'45'free'45'resp'45''8839'_872 v15 v16 v17 v18
du_collision'45'free'45'resp'45''8839'_872 ::
  T_State'7501'_536 ->
  T_State'7501'_536 ->
  T_CollisionFree_820 ->
  ( T_Message_62 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
  ) ->
  T_CollisionFree_820
du_collision'45'free'45'resp'45''8839'_872 v0 v1 v2 v3 =
  case coe v2 of
    C_collision'45'free_834 v4 v5 v6 ->
      coe
        C_collision'45'free_834
        (coe v4)
        (coe v5)
        ( coe
            MAlonzo.Code.Data.List.Relation.Binary.Subset.Propositional.Properties.du_All'45'resp'45''8839'_214
            ( coe
                MAlonzo.Code.Data.List.Base.du_cartesianProduct_112
                (d_history_554 (coe v1))
                (d_history_554 (coe v1))
            )
            ( coe
                MAlonzo.Code.Data.List.Base.du_cartesianProduct_112
                (d_history_554 (coe v0))
                (d_history_554 (coe v0))
            )
            ( \v7 v8 ->
                coe
                  MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45'cartesianProduct'8314'_360
                  (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v7))
                  (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v7))
                  (d_history_554 (coe v1))
                  (d_history_554 (coe v1))
                  ( coe
                      v3
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v7))
                      ( MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          ( coe
                              MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45'cartesianProduct'8315'_372
                              (coe d_history_554 (coe v0))
                              (coe d_history_554 (coe v0))
                              (coe v7)
                              (coe v8)
                          )
                      )
                  )
                  ( coe
                      v3
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v7))
                      ( MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          ( coe
                              MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45'cartesianProduct'8315'_372
                              (coe d_history_554 (coe v0))
                              (coe d_history_554 (coe v0))
                              (coe v7)
                              (coe v8)
                          )
                      )
                  )
            )
            v6
        )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._._.[]-hist-common-prefix
d_'91''93''45'hist'45'common'45'prefix_892 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_536 ->
  T_State'7501'_536 ->
  Integer ->
  MAlonzo.Code.Peras.Block.T_Honesty_26 ->
  T_Message_62 ->
  T__'8866'_'91'_'93''8640'__610 ->
  T_Message_62 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_'91''93''45'hist'45'common'45'prefix_892
  ~v0
  ~v1
  ~v2
  ~v3
  ~v4
  ~v5
  ~v6
  ~v7
  ~v8
  ~v9
  ~v10
  ~v11
  ~v12
  ~v13
  ~v14
  ~v15
  ~v16
  ~v17
  ~v18
  ~v19
  v20
  ~v21
  v22 =
    du_'91''93''45'hist'45'common'45'prefix_892 v20 v22
du_'91''93''45'hist'45'common'45'prefix_892 ::
  T__'8866'_'91'_'93''8640'__610 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_'91''93''45'hist'45'common'45'prefix_892 v0 v1 =
  coe seq (coe v0) (coe v1)

-- Peras.SmallStep._._.[]⇀-collision-free
d_'91''93''8640''45'collision'45'free_908 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_536 ->
  T_State'7501'_536 ->
  Integer ->
  MAlonzo.Code.Peras.Block.T_Honesty_26 ->
  T_Message_62 ->
  T_CollisionFree_820 ->
  T__'8866'_'91'_'93''8640'__610 ->
  T_CollisionFree_820
d_'91''93''8640''45'collision'45'free_908
  ~v0
  ~v1
  ~v2
  ~v3
  ~v4
  ~v5
  ~v6
  ~v7
  ~v8
  ~v9
  ~v10
  ~v11
  ~v12
  ~v13
  ~v14
  ~v15
  ~v16
  ~v17
  ~v18
  ~v19
  v20
  v21 =
    du_'91''93''8640''45'collision'45'free_908 v20 v21
du_'91''93''8640''45'collision'45'free_908 ::
  T_CollisionFree_820 ->
  T__'8866'_'91'_'93''8640'__610 ->
  T_CollisionFree_820
du_'91''93''8640''45'collision'45'free_908 v0 v1 =
  coe seq (coe v0) (coe seq (coe v1) (coe v0))

-- Peras.SmallStep._._.[]↷-hist-common-prefix
d_'91''93''8631''45'hist'45'common'45'prefix_930 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_536 ->
  T_State'7501'_536 ->
  Integer ->
  MAlonzo.Code.Peras.Block.T_Honesty_26 ->
  T__'8866'_'8631'__692 ->
  T_Message_62 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_'91''93''8631''45'hist'45'common'45'prefix_930
  ~v0
  ~v1
  ~v2
  ~v3
  ~v4
  ~v5
  ~v6
  ~v7
  ~v8
  ~v9
  ~v10
  ~v11
  ~v12
  ~v13
  ~v14
  ~v15
  ~v16
  ~v17
  ~v18
  v19
  ~v20 =
    du_'91''93''8631''45'hist'45'common'45'prefix_930 v19
du_'91''93''8631''45'hist'45'common'45'prefix_930 ::
  T__'8866'_'8631'__692 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_'91''93''8631''45'hist'45'common'45'prefix_930 v0 =
  coe
    seq
    (coe v0)
    ( coe
        MAlonzo.Code.Data.List.Relation.Binary.Subset.Propositional.Properties.du_xs'8838'x'8759'xs_228
    )

-- Peras.SmallStep._._.[]⇉-hist-common-prefix
d_'91''93''8649''45'hist'45'common'45'prefix_948 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_536 ->
  T_State'7501'_536 ->
  Integer ->
  MAlonzo.Code.Peras.Block.T_Honesty_26 ->
  T__'8866'_'8649'__656 ->
  T_Message_62 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_'91''93''8649''45'hist'45'common'45'prefix_948
  ~v0
  ~v1
  ~v2
  ~v3
  ~v4
  ~v5
  ~v6
  ~v7
  ~v8
  ~v9
  ~v10
  ~v11
  ~v12
  ~v13
  ~v14
  ~v15
  ~v16
  ~v17
  ~v18
  v19
  ~v20 =
    du_'91''93''8649''45'hist'45'common'45'prefix_948 v19
du_'91''93''8649''45'hist'45'common'45'prefix_948 ::
  T__'8866'_'8649'__656 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_'91''93''8649''45'hist'45'common'45'prefix_948 v0 =
  coe
    seq
    (coe v0)
    ( coe
        MAlonzo.Code.Data.List.Relation.Binary.Subset.Propositional.Properties.du_xs'8838'x'8759'xs_228
    )

-- Peras.SmallStep._._.[]↷-collision-free
d_'91''93''8631''45'collision'45'free_962 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_536 ->
  T_State'7501'_536 ->
  Integer ->
  MAlonzo.Code.Peras.Block.T_Honesty_26 ->
  T_CollisionFree_820 ->
  T__'8866'_'8631'__692 ->
  T_CollisionFree_820
d_'91''93''8631''45'collision'45'free_962
  ~v0
  ~v1
  ~v2
  ~v3
  ~v4
  ~v5
  ~v6
  ~v7
  ~v8
  ~v9
  ~v10
  ~v11
  ~v12
  ~v13
  ~v14
  v15
  v16
  ~v17
  ~v18
  v19
  v20 =
    du_'91''93''8631''45'collision'45'free_962 v15 v16 v19 v20
du_'91''93''8631''45'collision'45'free_962 ::
  T_State'7501'_536 ->
  T_State'7501'_536 ->
  T_CollisionFree_820 ->
  T__'8866'_'8631'__692 ->
  T_CollisionFree_820
du_'91''93''8631''45'collision'45'free_962 v0 v1 v2 v3 =
  coe
    du_collision'45'free'45'resp'45''8839'_872
    (coe v0)
    (coe v1)
    (coe v2)
    ( \v4 ->
        coe du_'91''93''8631''45'hist'45'common'45'prefix_930 (coe v3)
    )

-- Peras.SmallStep._._.[]⇉-collision-free
d_'91''93''8649''45'collision'45'free_976 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_536 ->
  T_State'7501'_536 ->
  Integer ->
  MAlonzo.Code.Peras.Block.T_Honesty_26 ->
  T_CollisionFree_820 ->
  T__'8866'_'8649'__656 ->
  T_CollisionFree_820
d_'91''93''8649''45'collision'45'free_976
  ~v0
  ~v1
  ~v2
  ~v3
  ~v4
  ~v5
  ~v6
  ~v7
  ~v8
  ~v9
  ~v10
  ~v11
  ~v12
  ~v13
  ~v14
  v15
  v16
  ~v17
  ~v18
  v19
  v20 =
    du_'91''93''8649''45'collision'45'free_976 v15 v16 v19 v20
du_'91''93''8649''45'collision'45'free_976 ::
  T_State'7501'_536 ->
  T_State'7501'_536 ->
  T_CollisionFree_820 ->
  T__'8866'_'8649'__656 ->
  T_CollisionFree_820
du_'91''93''8649''45'collision'45'free_976 v0 v1 v2 v3 =
  coe
    du_collision'45'free'45'resp'45''8839'_872
    (coe v0)
    (coe v1)
    (coe v2)
    ( \v4 ->
        coe du_'91''93''8649''45'hist'45'common'45'prefix_948 (coe v3)
    )

-- Peras.SmallStep._._.↝-collision-free
d_'8605''45'collision'45'free_986 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_536 ->
  T_State'7501'_536 ->
  T__'8605'__780 ->
  T_CollisionFree_820 ->
  T_CollisionFree_820
d_'8605''45'collision'45'free_986
  ~v0
  ~v1
  ~v2
  ~v3
  ~v4
  ~v5
  ~v6
  ~v7
  ~v8
  ~v9
  ~v10
  ~v11
  ~v12
  ~v13
  ~v14
  v15
  v16
  v17
  v18 =
    du_'8605''45'collision'45'free_986 v15 v16 v17 v18
du_'8605''45'collision'45'free_986 ::
  T_State'7501'_536 ->
  T_State'7501'_536 ->
  T__'8605'__780 ->
  T_CollisionFree_820 ->
  T_CollisionFree_820
du_'8605''45'collision'45'free_986 v0 v1 v2 v3 =
  case coe v2 of
    C_Deliver_784 v4 v5 v8 v9 ->
      coe du_'91''93''8640''45'collision'45'free_908 (coe v3) (coe v9)
    C_CastVote_786 v4 v5 v8 ->
      coe
        du_'91''93''8649''45'collision'45'free_976
        (coe v0)
        (coe v1)
        (coe v3)
        (coe v8)
    C_CreateBlock_788 v4 v5 v8 ->
      coe
        du_'91''93''8631''45'collision'45'free_962
        (coe v0)
        (coe v1)
        (coe v3)
        (coe v8)
    C_NextSlot_790 v5 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._._.↝⋆-collision-free
d_'8605''8902''45'collision'45'free_1006 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_402 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_536 ->
  T_State'7501'_536 ->
  T__'8605''8902'__792 ->
  T_CollisionFree_820 ->
  T_CollisionFree_820
d_'8605''8902''45'collision'45'free_1006
  ~v0
  ~v1
  ~v2
  ~v3
  ~v4
  ~v5
  ~v6
  ~v7
  ~v8
  ~v9
  ~v10
  ~v11
  ~v12
  ~v13
  ~v14
  v15
  ~v16
  v17
  v18 =
    du_'8605''8902''45'collision'45'free_1006 v15 v17 v18
du_'8605''8902''45'collision'45'free_1006 ::
  T_State'7501'_536 ->
  T__'8605''8902'__792 ->
  T_CollisionFree_820 ->
  T_CollisionFree_820
du_'8605''8902''45'collision'45'free_1006 v0 v1 v2 =
  case coe v1 of
    C_'91''93''8242'_794 -> coe v2
    C__'8759''8242'__796 v4 v6 v7 ->
      coe
        du_'8605''45'collision'45'free_986
        (coe v0)
        (coe v4)
        (coe v6)
        ( coe
            du_'8605''8902''45'collision'45'free_1006
            (coe v4)
            (coe v7)
            (coe v2)
        )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._._.ForgingFree
d_ForgingFree_1018
  a0
  a1
  a2
  a3
  a4
  a5
  a6
  a7
  a8
  a9
  a10
  a11
  a12
  a13
  a14
  a15 =
    ()
data T_ForgingFree_1018
  = C_forging'45'free_1032
      T_State'7501'_536
      MAlonzo.Code.Peras.Block.T_Block_62
      Integer
      T__'8866'_'8631'__692
      MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
