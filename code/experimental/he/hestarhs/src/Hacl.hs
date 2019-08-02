{-# LANGUAGE ForeignFunctionInterface #-}

-- | Hacl bindings

module Hacl where

import Data.Word
import Foreign.Ptr
import System.IO


type Bignum = Ptr Word64

foreign import ccall "Hacl_Impl_Bignum_Addition_bn_sub" bn_sub
    :: Word32 -> Word32 -> Bignum -> Bignum -> Bignum -> IO ()
