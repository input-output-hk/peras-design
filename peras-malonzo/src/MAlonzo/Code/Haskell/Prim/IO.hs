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

module MAlonzo.Code.Haskell.Prim.IO where

import qualified Data.Text
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

-- Haskell.Prim.IO.IO
d_IO_8 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Prim.IO.IO"

-- Haskell.Prim.IO.FilePath
d_FilePath_10 :: ()
d_FilePath_10 = erased

-- Haskell.Prim.IO.interact
d_interact_12 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Prim.IO.interact"

-- Haskell.Prim.IO.getContents
d_getContents_14 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Prim.IO.getContents"

-- Haskell.Prim.IO.getLine
d_getLine_16 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Prim.IO.getLine"

-- Haskell.Prim.IO.getChar
d_getChar_18 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Prim.IO.getChar"

-- Haskell.Prim.IO.print
d_print_20 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Prim.IO.print"

-- Haskell.Prim.IO.putChar
d_putChar_22 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Prim.IO.putChar"

-- Haskell.Prim.IO.putStr
d_putStr_24 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Prim.IO.putStr"

-- Haskell.Prim.IO.putStrLn
d_putStrLn_26 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Prim.IO.putStrLn"

-- Haskell.Prim.IO.readFile
d_readFile_28 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Prim.IO.readFile"

-- Haskell.Prim.IO.writeFile
d_writeFile_30 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Prim.IO.writeFile"

-- Haskell.Prim.IO.appendFile
d_appendFile_32 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Prim.IO.appendFile"
