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

module MAlonzo.Code.Haskell.Prim.Show where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Float
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Haskell.Prim
import qualified MAlonzo.Code.Haskell.Prim.Either
import qualified MAlonzo.Code.Haskell.Prim.Foldable
import qualified MAlonzo.Code.Haskell.Prim.Int
import qualified MAlonzo.Code.Haskell.Prim.Integer
import qualified MAlonzo.Code.Haskell.Prim.List
import qualified MAlonzo.Code.Haskell.Prim.Maybe
import qualified MAlonzo.Code.Haskell.Prim.Tuple
import qualified MAlonzo.Code.Haskell.Prim.Word
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

-- Haskell.Prim.Show.ShowS
d_ShowS_6 :: ()
d_ShowS_6 = erased

-- Haskell.Prim.Show.showChar
d_showChar_8 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_showChar_8 = coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22

-- Haskell.Prim.Show.showString
d_showString_10 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_showString_10 =
  coe MAlonzo.Code.Haskell.Prim.List.du__'43''43'__20

-- Haskell.Prim.Show.showParen
d_showParen_12 ::
  Bool ->
  ( [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
    [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_showParen_12 v0 v1 =
  if coe v0
    then
      coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        ( coe
            d_showString_10
            ( coe
                MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                ("(" :: Data.Text.Text)
            )
        )
        ( coe
            MAlonzo.Code.Haskell.Prim.du__'8728'__28
            (coe v1)
            ( coe
                d_showString_10
                ( coe
                    MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                    (")" :: Data.Text.Text)
                )
            )
        )
    else coe v1

-- Haskell.Prim.Show.defaultShowList
d_defaultShowList_18 ::
  () ->
  ( AgdaAny ->
    [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
    [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
  ) ->
  [AgdaAny] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_defaultShowList_18 ~v0 v1 v2 = du_defaultShowList_18 v1 v2
du_defaultShowList_18 ::
  ( AgdaAny ->
    [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
    [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
  ) ->
  [AgdaAny] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
du_defaultShowList_18 v0 v1 =
  case coe v1 of
    [] ->
      coe
        d_showString_10
        ( coe
            MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
            ("[]" :: Data.Text.Text)
        )
    (:) v2 v3 ->
      coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        ( coe
            d_showString_10
            ( coe
                MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                ("[" :: Data.Text.Text)
            )
        )
        ( coe
            MAlonzo.Code.Haskell.Prim.du__'8728'__28
            ( coe
                MAlonzo.Code.Haskell.Prim.Foldable.du_foldl_170
                ( coe
                    MAlonzo.Code.Haskell.Prim.Foldable.C_DefaultFoldable'46'constructor_4805
                    ( \v4 v5 v6 v7 v8 ->
                        coe
                          MAlonzo.Code.Haskell.Prim.Foldable.du_foldMapList_408
                          v6
                          v7
                          v8
                    )
                )
                ( coe
                    ( \v4 v5 ->
                        coe
                          MAlonzo.Code.Haskell.Prim.du__'8728'__28
                          (coe v4)
                          ( coe
                              MAlonzo.Code.Haskell.Prim.du__'8728'__28
                              ( coe
                                  d_showString_10
                                  ( coe
                                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                      ("," :: Data.Text.Text)
                                  )
                              )
                              (coe v0 v5)
                          )
                    )
                )
                (coe v0 v2)
                (coe v3)
            )
            ( coe
                d_showString_10
                ( coe
                    MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                    ("]" :: Data.Text.Text)
                )
            )
        )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Show.Show
d_Show_34 a0 = ()
data T_Show_34
  = C_Show'46'constructor_1859
      ( MAlonzo.Code.Haskell.Prim.Int.T_Int_6 ->
        AgdaAny ->
        [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
        [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
      )
      ( [AgdaAny] ->
        [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
        [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
      )
      (AgdaAny -> [MAlonzo.Code.Agda.Builtin.Char.T_Char_6])

-- Haskell.Prim.Show.Show.showsPrec
d_showsPrec_44 ::
  T_Show_34 ->
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_showsPrec_44 v0 =
  case coe v0 of
    C_Show'46'constructor_1859 v1 v2 v3 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Show.Show.showList
d_showList_46 ::
  T_Show_34 ->
  [AgdaAny] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_showList_46 v0 =
  case coe v0 of
    C_Show'46'constructor_1859 v1 v2 v3 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Show.Show.show
d_show_48 ::
  T_Show_34 -> AgdaAny -> [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_show_48 v0 =
  case coe v0 of
    C_Show'46'constructor_1859 v1 v2 v3 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Show.Show₁
d_Show'8321'_52 a0 = ()
newtype T_Show'8321'_52
  = C_Show'8321''46'constructor_1957
      ( MAlonzo.Code.Haskell.Prim.Int.T_Int_6 ->
        AgdaAny ->
        [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
        [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
      )

-- Haskell.Prim.Show.Show₁.showsPrec
d_showsPrec_58 ::
  T_Show'8321'_52 ->
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_showsPrec_58 v0 =
  case coe v0 of
    C_Show'8321''46'constructor_1957 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Show.Show₁.show
d_show_60 ::
  () ->
  T_Show'8321'_52 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_show_60 ~v0 v1 v2 = du_show_60 v1 v2
du_show_60 ::
  T_Show'8321'_52 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
du_show_60 v0 v1 =
  coe
    d_showsPrec_58
    v0
    ( coe
        MAlonzo.Code.Haskell.Prim.Int.C_int64_8
        (coe (0 :: MAlonzo.RTE.Word64))
    )
    v1
    ( coe
        MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
        ("" :: Data.Text.Text)
    )

-- Haskell.Prim.Show.Show₁.showList
d_showList_64 ::
  () ->
  T_Show'8321'_52 ->
  [AgdaAny] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_showList_64 ~v0 v1 = du_showList_64 v1
du_showList_64 ::
  T_Show'8321'_52 ->
  [AgdaAny] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
du_showList_64 v0 =
  coe
    du_defaultShowList_18
    ( coe
        d_showsPrec_58
        v0
        ( coe
            MAlonzo.Code.Haskell.Prim.Int.C_int64_8
            (coe (0 :: MAlonzo.RTE.Word64))
        )
    )

-- Haskell.Prim.Show.Show₂
d_Show'8322'_68 a0 = ()
newtype T_Show'8322'_68
  = C_Show'8322''46'constructor_2443
      ( AgdaAny ->
        [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
      )

-- Haskell.Prim.Show.Show₂.show
d_show_74 ::
  T_Show'8322'_68 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_show_74 v0 =
  case coe v0 of
    C_Show'8322''46'constructor_2443 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Show.Show₂.showsPrec
d_showsPrec_76 ::
  () ->
  T_Show'8322'_68 ->
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_showsPrec_76 ~v0 v1 ~v2 v3 v4 = du_showsPrec_76 v1 v3 v4
du_showsPrec_76 ::
  T_Show'8322'_68 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
du_showsPrec_76 v0 v1 v2 =
  coe
    MAlonzo.Code.Haskell.Prim.List.du__'43''43'__20
    (coe d_show_74 v0 v1)
    (coe v2)

-- Haskell.Prim.Show.Show₂.showList
d_showList_82 ::
  () ->
  T_Show'8322'_68 ->
  [AgdaAny] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_showList_82 ~v0 v1 = du_showList_82 v1
du_showList_82 ::
  T_Show'8322'_68 ->
  [AgdaAny] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
du_showList_82 v0 =
  coe du_defaultShowList_18 (coe du_showsPrec_76 (coe v0))

-- Haskell.Prim.Show._.show
d_show_86 ::
  T_Show_34 -> AgdaAny -> [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_show_86 v0 = coe d_show_48 (coe v0)

-- Haskell.Prim.Show._.showList
d_showList_88 ::
  T_Show_34 ->
  [AgdaAny] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_showList_88 v0 = coe d_showList_46 (coe v0)

-- Haskell.Prim.Show._.showsPrec
d_showsPrec_90 ::
  T_Show_34 ->
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_showsPrec_90 v0 = coe d_showsPrec_44 (coe v0)

-- Haskell.Prim.Show.shows
d_shows_92 ::
  () ->
  T_Show_34 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_shows_92 ~v0 v1 = du_shows_92 v1
du_shows_92 ::
  T_Show_34 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
du_shows_92 v0 =
  coe
    d_showsPrec_44
    v0
    ( coe
        MAlonzo.Code.Haskell.Prim.Int.C_int64_8
        (coe (0 :: MAlonzo.RTE.Word64))
    )

-- Haskell.Prim.Show.showsPrec=_
d_showsPrec'61'__94 ::
  () ->
  ( MAlonzo.Code.Haskell.Prim.Int.T_Int_6 ->
    AgdaAny ->
    [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
    [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
  ) ->
  T_Show_34
d_showsPrec'61'__94 ~v0 v1 = du_showsPrec'61'__94 v1
du_showsPrec'61'__94 ::
  ( MAlonzo.Code.Haskell.Prim.Int.T_Int_6 ->
    AgdaAny ->
    [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
    [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
  ) ->
  T_Show_34
du_showsPrec'61'__94 v0 =
  coe
    C_Show'46'constructor_1859
    (coe v0)
    ( coe
        du_showList_64
        (coe C_Show'8321''46'constructor_1957 (coe v0))
    )
    (coe du_show_60 (coe C_Show'8321''46'constructor_1957 (coe v0)))

-- Haskell.Prim.Show._.show
d_show_102 ::
  () ->
  ( MAlonzo.Code.Haskell.Prim.Int.T_Int_6 ->
    AgdaAny ->
    [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
    [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
  ) ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_show_102 ~v0 v1 = du_show_102 v1
du_show_102 ::
  ( MAlonzo.Code.Haskell.Prim.Int.T_Int_6 ->
    AgdaAny ->
    [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
    [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
  ) ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
du_show_102 v0 =
  coe du_show_60 (coe C_Show'8321''46'constructor_1957 (coe v0))

-- Haskell.Prim.Show._.showList
d_showList_104 ::
  () ->
  ( MAlonzo.Code.Haskell.Prim.Int.T_Int_6 ->
    AgdaAny ->
    [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
    [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
  ) ->
  [AgdaAny] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_showList_104 ~v0 v1 = du_showList_104 v1
du_showList_104 ::
  ( MAlonzo.Code.Haskell.Prim.Int.T_Int_6 ->
    AgdaAny ->
    [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
    [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
  ) ->
  [AgdaAny] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
du_showList_104 v0 =
  coe
    du_showList_64
    (coe C_Show'8321''46'constructor_1957 (coe v0))

-- Haskell.Prim.Show.show=_
d_show'61'__108 ::
  () ->
  (AgdaAny -> [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]) ->
  T_Show_34
d_show'61'__108 ~v0 v1 = du_show'61'__108 v1
du_show'61'__108 ::
  (AgdaAny -> [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]) -> T_Show_34
du_show'61'__108 v0 =
  coe
    C_Show'46'constructor_1859
    ( \v1 v2 v3 ->
        coe
          du_showsPrec_76
          (coe C_Show'8322''46'constructor_2443 (coe v0))
          v2
          v3
    )
    ( coe
        du_showList_82
        (coe C_Show'8322''46'constructor_2443 (coe v0))
    )
    (coe v0)

-- Haskell.Prim.Show._.showList
d_showList_118 ::
  () ->
  (AgdaAny -> [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]) ->
  [AgdaAny] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_showList_118 ~v0 v1 = du_showList_118 v1
du_showList_118 ::
  (AgdaAny -> [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]) ->
  [AgdaAny] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
du_showList_118 v0 =
  coe
    du_showList_82
    (coe C_Show'8322''46'constructor_2443 (coe v0))

-- Haskell.Prim.Show._.showsPrec
d_showsPrec_120 ::
  () ->
  (AgdaAny -> [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]) ->
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_showsPrec_120 ~v0 v1 = du_showsPrec_120 v1
du_showsPrec_120 ::
  (AgdaAny -> [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]) ->
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
du_showsPrec_120 v0 v1 v2 v3 =
  coe
    du_showsPrec_76
    (coe C_Show'8322''46'constructor_2443 (coe v0))
    v2
    v3

-- Haskell.Prim.Show.iShowNat
d_iShowNat_122 :: T_Show_34
d_iShowNat_122 =
  coe
    du_show'61'__108
    ( coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12)
        (coe MAlonzo.Code.Agda.Builtin.String.d_primShowNat_24)
    )

-- Haskell.Prim.Show.iShowInteger
d_iShowInteger_124 :: T_Show_34
d_iShowInteger_124 =
  coe
    du_show'61'__108
    (coe MAlonzo.Code.Haskell.Prim.Integer.d_showInteger_104)

-- Haskell.Prim.Show.iShowInt
d_iShowInt_126 :: T_Show_34
d_iShowInt_126 =
  coe
    du_show'61'__108
    (coe MAlonzo.Code.Haskell.Prim.Int.d_showInt_118)

-- Haskell.Prim.Show.iShowWord
d_iShowWord_128 :: T_Show_34
d_iShowWord_128 =
  coe
    du_show'61'__108
    (coe MAlonzo.Code.Haskell.Prim.Word.d_showWord_48)

-- Haskell.Prim.Show.iShowDouble
d_iShowDouble_130 :: T_Show_34
d_iShowDouble_130 =
  coe
    du_show'61'__108
    ( coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12)
        (coe MAlonzo.Code.Agda.Builtin.Float.d_primShowFloat_46)
    )

-- Haskell.Prim.Show.iShowBool
d_iShowBool_132 :: T_Show_34
d_iShowBool_132 =
  coe
    du_show'61'__108
    ( coe
        ( \v0 ->
            if coe v0
              then
                coe
                  MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                  ("True" :: Data.Text.Text)
              else
                coe
                  MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                  ("False" :: Data.Text.Text)
        )
    )

-- Haskell.Prim.Show.iShowChar
d_iShowChar_136 :: T_Show_34
d_iShowChar_136 =
  coe
    du_showsPrec'61'__94
    ( coe
        ( \v0 ->
            coe
              MAlonzo.Code.Haskell.Prim.du__'8728'__28
              (coe d_showString_10)
              ( coe
                  MAlonzo.Code.Haskell.Prim.du__'8728'__28
                  (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12)
                  (coe MAlonzo.Code.Agda.Builtin.String.d_primShowChar_20)
              )
        )
    )

-- Haskell.Prim.Show.iShowList
d_iShowList_140 :: () -> T_Show_34 -> T_Show_34
d_iShowList_140 ~v0 v1 = du_iShowList_140 v1
du_iShowList_140 :: T_Show_34 -> T_Show_34
du_iShowList_140 v0 =
  coe du_showsPrec'61'__94 (coe (\v1 -> d_showList_46 (coe v0)))

-- Haskell.Prim.Show.showApp₁
d_showApp'8321'_144 ::
  () ->
  T_Show_34 ->
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_showApp'8321'_144 ~v0 v1 v2 v3 v4 =
  du_showApp'8321'_144 v1 v2 v3 v4
du_showApp'8321'_144 ::
  T_Show_34 ->
  MAlonzo.Code.Haskell.Prim.Int.T_Int_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
du_showApp'8321'_144 v0 v1 v2 v3 =
  coe
    MAlonzo.Code.Haskell.Prim.du__'36'__48
    ( coe
        d_showParen_12
        ( coe
            MAlonzo.Code.Haskell.Prim.Int.d_ltInt_66
            ( coe
                MAlonzo.Code.Haskell.Prim.Int.C_int64_8
                (coe (10 :: MAlonzo.RTE.Word64))
            )
            (coe v1)
        )
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        (coe d_showString_10 v2)
        ( coe
            MAlonzo.Code.Haskell.Prim.du__'8728'__28
            ( coe
                d_showString_10
                ( coe
                    MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                    (" " :: Data.Text.Text)
                )
            )
            ( coe
                d_showsPrec_44
                v0
                ( coe
                    MAlonzo.Code.Haskell.Prim.Int.C_int64_8
                    (coe (11 :: MAlonzo.RTE.Word64))
                )
                v3
            )
        )
    )

-- Haskell.Prim.Show.iShowMaybe
d_iShowMaybe_152 :: () -> T_Show_34 -> T_Show_34
d_iShowMaybe_152 ~v0 v1 = du_iShowMaybe_152 v1
du_iShowMaybe_152 :: T_Show_34 -> T_Show_34
du_iShowMaybe_152 v0 =
  coe
    du_showsPrec'61'__94
    ( coe
        ( \v1 v2 ->
            case coe v2 of
              MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16 ->
                coe
                  d_showString_10
                  ( coe
                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                      ("Nothing" :: Data.Text.Text)
                  )
              MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 v3 ->
                coe
                  du_showApp'8321'_144
                  (coe v0)
                  (coe v1)
                  ( coe
                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                      ("Just" :: Data.Text.Text)
                  )
                  (coe v3)
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Haskell.Prim.Show.iShowEither
d_iShowEither_162 ::
  () -> () -> T_Show_34 -> T_Show_34 -> T_Show_34
d_iShowEither_162 ~v0 ~v1 v2 v3 = du_iShowEither_162 v2 v3
du_iShowEither_162 :: T_Show_34 -> T_Show_34 -> T_Show_34
du_iShowEither_162 v0 v1 =
  coe
    du_showsPrec'61'__94
    ( coe
        ( \v2 v3 ->
            case coe v3 of
              MAlonzo.Code.Haskell.Prim.Either.C_Left_16 v4 ->
                coe
                  du_showApp'8321'_144
                  (coe v0)
                  (coe v2)
                  ( coe
                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                      ("Left" :: Data.Text.Text)
                  )
                  (coe v4)
              MAlonzo.Code.Haskell.Prim.Either.C_Right_18 v4 ->
                coe
                  du_showApp'8321'_144
                  (coe v1)
                  (coe v2)
                  ( coe
                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                      ("Right" :: Data.Text.Text)
                  )
                  (coe v4)
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Haskell.Prim.Show.iShowTuple₂
d_iShowTuple'8322'_174 ::
  () -> () -> T_Show_34 -> T_Show_34 -> T_Show_34
d_iShowTuple'8322'_174 ~v0 ~v1 v2 v3 =
  du_iShowTuple'8322'_174 v2 v3
du_iShowTuple'8322'_174 :: T_Show_34 -> T_Show_34 -> T_Show_34
du_iShowTuple'8322'_174 v0 v1 =
  coe
    du_showsPrec'61'__94
    ( coe
        ( \v2 v3 ->
            case coe v3 of
              MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24 v4 v5 ->
                coe
                  MAlonzo.Code.Haskell.Prim.du__'8728'__28
                  ( coe
                      d_showString_10
                      ( coe
                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                          ("(" :: Data.Text.Text)
                      )
                  )
                  ( coe
                      MAlonzo.Code.Haskell.Prim.du__'8728'__28
                      (coe du_shows_92 v0 v4)
                      ( coe
                          MAlonzo.Code.Haskell.Prim.du__'8728'__28
                          ( coe
                              d_showString_10
                              ( coe
                                  MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                  (", " :: Data.Text.Text)
                              )
                          )
                          ( coe
                              MAlonzo.Code.Haskell.Prim.du__'8728'__28
                              (coe du_shows_92 v1 v5)
                              ( coe
                                  d_showString_10
                                  ( coe
                                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                      (")" :: Data.Text.Text)
                                  )
                              )
                          )
                      )
                  )
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Haskell.Prim.Show.iShowTuple₃
d_iShowTuple'8323'_184 ::
  () -> () -> () -> T_Show_34 -> T_Show_34 -> T_Show_34 -> T_Show_34
d_iShowTuple'8323'_184 ~v0 ~v1 ~v2 v3 v4 v5 =
  du_iShowTuple'8323'_184 v3 v4 v5
du_iShowTuple'8323'_184 ::
  T_Show_34 -> T_Show_34 -> T_Show_34 -> T_Show_34
du_iShowTuple'8323'_184 v0 v1 v2 =
  coe
    du_showsPrec'61'__94
    ( coe
        ( \v3 v4 ->
            case coe v4 of
              MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40 v5 v6 v7 ->
                coe
                  MAlonzo.Code.Haskell.Prim.du__'8728'__28
                  ( coe
                      d_showString_10
                      ( coe
                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                          ("(" :: Data.Text.Text)
                      )
                  )
                  ( coe
                      MAlonzo.Code.Haskell.Prim.du__'8728'__28
                      (coe du_shows_92 v0 v5)
                      ( coe
                          MAlonzo.Code.Haskell.Prim.du__'8728'__28
                          ( coe
                              d_showString_10
                              ( coe
                                  MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                  (", " :: Data.Text.Text)
                              )
                          )
                          ( coe
                              MAlonzo.Code.Haskell.Prim.du__'8728'__28
                              (coe du_shows_92 v1 v6)
                              ( coe
                                  MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                  ( coe
                                      d_showString_10
                                      ( coe
                                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                          (", " :: Data.Text.Text)
                                      )
                                  )
                                  ( coe
                                      MAlonzo.Code.Haskell.Prim.du__'8728'__28
                                      (coe du_shows_92 v2 v7)
                                      ( coe
                                          d_showString_10
                                          ( coe
                                              MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                              (")" :: Data.Text.Text)
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
