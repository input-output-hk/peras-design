{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeApplications #-}

module Peras.Node where

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Foreign (
  Ptr,
  Storable (alignment, peek, poke, sizeOf),
  Word64,
  Word8,
  new,
  newArray,
  nullPtr,
  plusPtr,
  with,
 )
import Foreign.C.Types

type Address = Word64

data ByteBuffer = ByteBuffer
  { bufferSize :: Word64
  , bytes :: Ptr Word8
  }

instance Storable ByteBuffer where
  sizeOf _ = sizeOf @Word64 undefined + sizeOf @Word undefined
  alignment _ = alignment @CInt undefined

  poke addr ByteBuffer{bufferSize, bytes} = do
    poke (addr `plusPtr` 0) bufferSize
    poke (addr `plusPtr` sizeOf bytes) bytes

  peek addr =
    ByteBuffer
      <$> peek (addr `plusPtr` 0)
      <*> peek (addr `plusPtr` sizeOf @Word64 undefined)

sendFfi :: Address -> ByteString -> IO Bool
sendFfi address bs = do
  bytes <- newArray (BS.unpack bs)
  let buffer =
        ByteBuffer
          { bufferSize = fromIntegral $ BS.length bs
          , bytes
          }
  with buffer (pure . send_ffi address)

receiveFfi :: IO (Either String (ByteBuffer, Address))
receiveFfi = do
  bufferP <- new ByteBuffer{bufferSize = 0, bytes = nullPtr}
  addrP <- new @Address 0
  let res = receive_ffi bufferP addrP
  if res
    then Right <$> ((,) <$> peek bufferP <*> peek addrP)
    else pure $ Left "fail to receive data"

foreign import capi unsafe "netsim.h" send_ffi :: Address -> Ptr ByteBuffer -> Bool

foreign import capi unsafe "netsim.h" receive_ffi :: Ptr ByteBuffer -> Ptr Address -> Bool
