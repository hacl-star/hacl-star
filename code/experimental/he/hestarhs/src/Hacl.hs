{-# LANGUAGE CApiFFI                  #-}
{-# LANGUAGE ForeignFunctionInterface #-}

-- | Hacl bindings

module Hacl where

import Universum

import Foreign.StablePtr
import Foreign.Storable (Storable (..))

----------------------------------------------------------------------------
-- Bignums
----------------------------------------------------------------------------

type Bignum = Ptr Word64

foreign import ccall "Hacl_Impl_Bignum_Comparison_bn_is_less" bnIsLess
    :: Word32 -> Word32 -> Bignum -> Bignum -> IO Bool

foreign import ccall "Hacl_Impl_Bignum_Comparison_bn_is_equal" bnIsEqual
    :: Word32 -> Word32 -> Bignum -> Bignum -> IO Bool

foreign import ccall "Hacl_Impl_Bignum_Comparison_bn_is_greater" bnIsGreater
    :: Word32 -> Word32 -> Bignum -> Bignum -> IO Bool

foreign import ccall "Hacl_Impl_Bignum_Comparison_bn_is_zero" bnIsZero
    :: Word32 -> Word32 -> Bignum -> Bignum -> IO Bool

foreign import ccall "Hacl_Impl_Bignum_Addition_bn_sub" bnSub
    :: Word32 -> Word32 -> Bignum -> Bignum -> Bignum -> IO ()

foreign import ccall "Hacl_Impl_Bignum_Addition_bn_sub_exact" bnSubExact
    :: Word32 -> Word32 -> Bignum -> Bignum -> Bignum -> IO ()

foreign import ccall "Hacl_Impl_Bignum_Addition_bn_add" bnAdd
    :: Word32 -> Word32 -> Bignum -> Bignum -> Bignum -> IO ()

foreign import ccall "Hacl_Impl_Bignum_Addition_bn_add_fitting" bnAddFitting
    :: Word32 -> Word32 -> Bignum -> Bignum -> Bignum -> IO ()

foreign import ccall "Hacl_Impl_Bignum_Addition_bn_add_exact" bnAddExact
    :: Word32 -> Word32 -> Bignum -> Bignum -> Bignum -> IO ()

foreign import ccall "Hacl_Impl_Bignum_Multiplication_bn_mul_fitting" bnMulFitting
    :: Word32 -> Word32 -> Word32 -> Bignum -> Bignum -> Bignum -> IO ()

foreign import ccall "Hacl_Impl_Bignum_Division_bn_divide" bnDivide
    :: Word32 -> Bignum -> Bignum -> Bignum -> IO ()

foreign import ccall "Hacl_Impl_Bignum_Exponentiation_bn_exp" bnExp
    :: Word32 -> Word32 -> Bignum -> Bignum -> Bignum -> IO ()

foreign import ccall "Hacl_Impl_Bignum_Modular_bn_remainder" bnRemainder
    :: Word32 -> Word32 -> Bignum -> Bignum -> Bignum -> IO ()

foreign import ccall "Hacl_Impl_Bignum_Modular_bn_modular_add" bnModAdd
    :: Word32 -> Bignum -> Bignum -> Bignum -> Bignum -> IO ()

foreign import ccall "Hacl_Impl_Bignum_Modular_bn_modular_sub" bnModSub
    :: Word32 -> Bignum -> Bignum -> Bignum -> Bignum -> IO ()

foreign import ccall "Hacl_Impl_Bignum_Modular_bn_modular_mul" bnModMul
    :: Word32 -> Bignum -> Bignum -> Bignum -> Bignum -> IO ()

foreign import ccall "Hacl_Impl_Bignum_Modular_bn_modular_exp" bnModExp
    :: Word32 -> Word32 -> Bignum -> Bignum -> Bignum -> Bignum -> IO ()

----------------------------------------------------------------------------
-- Paillier
----------------------------------------------------------------------------

foreign import ccall "Hacl_Impl_HE_Paillier_encrypt" paillierEnc
    :: Word32 -> Bignum -> Bignum -> Bignum -> Bignum -> Bignum -> Bignum -> IO ()

foreign import ccall "Hacl_Impl_HE_Paillier_to_secret" paillierToSec
    :: Word32
    -> Bignum -> Bignum -> Bignum -> Bignum
    -> Bignum -> Bignum -> Bignum
    -> IO ()

foreign import ccall "Hacl_Impl_HE_Paillier_decrypt" paillierDec
    :: Word32
    -> Bignum -> Bignum -> Bignum -> Bignum
    -> Bignum -> Bignum -> Bignum -> Bignum
    -> Bignum
    -> IO ()

foreign import ccall "Hacl_Impl_HE_Paillier_hom_add" paillierHomAdd
    :: Word32 -> Word32 -> Bignum -> Bignum -> Bignum -> Bignum -> Bignum -> IO ()

foreign import ccall "Hacl_Impl_HE_Paillier_hom_mul_plain" paillierHomMulScal
    :: Word32 -> Word32 -> Bignum -> Bignum -> Bignum -> Bignum -> Bignum -> IO ()
