{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies      #-}

-- | Packed AHE class.

module Hacl.Pahe
    ( Pahe(..)
    , paheRerand
    ) where

import Universum


-- TODO variable security level
class Pahe s where
    data PaheCiph s :: *
    data PaheSk s :: *
    data PahePk s :: *

    -- The number of elements we want to work over SIMD and their modulus
    paheKeyGen      :: Int -> Integer -> IO (PaheSk s)
    -- The length of vector inside
    paheK           :: PahePk s -> Int
    paheToPlaintext :: PahePk s -> [Integer] -> [Integer]
    paheToPublic    :: PaheSk s -> PahePk s

    paheZero        :: PahePk s -> PaheCiph s
    paheOne         :: PahePk s -> PaheCiph s
    paheMinOne      :: PahePk s -> PaheCiph s

    paheEnc         :: PahePk s -> [Integer] -> IO (PaheCiph s)
    paheDec         :: PaheSk s -> PaheCiph s -> IO [Integer]

    paheNeg         :: PahePk s -> PaheCiph s -> IO (PaheCiph s)
    default paheNeg :: Pahe s => PahePk s -> PaheCiph s -> IO (PaheCiph s)
    paheNeg pk ciph = paheSIMDMulScal pk ciph $ replicate (paheK pk) (-1)

    paheSIMDAdd     :: PahePk s -> PaheCiph s -> PaheCiph s -> IO (PaheCiph s)

    paheSIMDSub     :: PahePk s -> PaheCiph s -> PaheCiph s -> IO (PaheCiph s)
    default paheSIMDSub :: Pahe s => PahePk s -> PaheCiph s -> PaheCiph s -> IO (PaheCiph s)
    paheSIMDSub pk c1 c2 = paheSIMDAdd pk c1 =<< paheNeg pk c2

    paheSIMDMulScal :: PahePk s -> PaheCiph s -> [Integer] -> IO (PaheCiph s)

    paheMultBlind   :: PahePk s -> PaheCiph s -> IO (PaheCiph s)

    paheIsZero      :: PaheSk s -> PaheCiph s -> IO [Bool]
    default paheIsZero :: Pahe s => PaheSk s -> PaheCiph s -> IO [Bool]
    paheIsZero sk ciph = map (== 0) <$> paheDec sk ciph

    paheToBS        :: PahePk s -> PaheCiph s -> IO ByteString
    paheFromBS      :: PahePk s -> ByteString -> IO (PaheCiph s)

    -- This is a weird interface hack, which emulates the permutation
    -- in the "protocol" way, since for Paillier and GM we can just
    -- permute slots. But for DGK the only way to do permutation is to
    -- run the permutation protocol.
    --
    -- We're only using this method with paillier, but (potentially)
    -- also aiming for DGK.
    --
    -- The permutation acts on two ciphertexts passed and produces two
    -- (permuted) ciphertexts.
    pahePermute     :: PahePk s -> PaheCiph s -> PaheCiph s -> [Int] -> IO (PaheCiph s, PaheCiph s)
    pahePermuteServ :: PaheSk s -> IO ()


paheRerand :: Pahe s => PahePk s -> PaheCiph s -> IO (PaheCiph s)
paheRerand pk c = paheSIMDAdd pk c =<< paheEnc pk (replicate (paheK pk) 0)
