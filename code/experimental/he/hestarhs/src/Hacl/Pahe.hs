{-# LANGUAGE TypeFamilies #-}

-- | Class wrapper for packed AHE

module Hacl.Pahe where

import Universum

import Data.List ((!!))
import System.Random (randomRIO)

import Hacl.Bignum
import Hacl.Raw
import Hacl.Support
import Lib.Misc (suchThat)

----------------------------------------------------------------------------
-- Class definition
----------------------------------------------------------------------------

-- TODO variable security level
class Pahe s where
    data PaheCiph s :: *
    data PaheSk s :: *
    data PahePk s :: *

    paheKeyGen      :: Int -> IO (PaheSk s)
    paheToPublic    :: PaheSk s -> PahePk s
    paheEnc         :: PahePk s -> [Integer] -> IO (PaheCiph s)
    paheDec         :: PaheSk s -> PaheCiph s -> IO [Integer]
    paheSIMDAdd     :: PahePk s -> PaheCiph s -> PaheCiph s -> IO (PaheCiph s)
    paheSIMDMulScal :: PahePk s -> PaheCiph s -> [Integer] -> IO (PaheCiph s)

----------------------------------------------------------------------------
-- Paillier
----------------------------------------------------------------------------

data PailSep

instance Pahe PailSep where
    data PaheCiph PailSep = PailCiph [Bignum]
    data PaheSk PailSep =
           PailSepSk { pss_simdn :: Int
                     , pss_bn :: Word32
                     , pss_p :: Bignum
                     , pss_q :: Bignum
                     , pss_n :: Bignum
                     , pss_n_raw :: Integer
                     , pss_n2 :: Bignum
                     , pss_g :: Bignum
                     , pss_lambda :: Bignum
                     , pss_l2inv :: Bignum
                     }
    data PahePk PailSep =
           PailSepPk { psp_simdn :: Int
                     , psp_bn :: Word32
                     , psp_n :: Bignum
                     , psp_n_raw :: Integer
                     , psp_n2 :: Bignum
                     , psp_g :: Bignum
                     }

    paheKeyGen pss_simdn = do
        (p,q,_,_,_) <- genDataPaillier 1024
        let n = p * q
        let pss_n_raw = n
        let pss_bn = fromIntegral $ length $ inbase b64 (n*n)

        pss_p <- toBignum pss_bn p
        pss_q <- toBignum pss_bn q
        pss_n <- toBignum pss_bn n
        pss_n2 <- toBignum pss_bn (n*n)
        pss_g <- toBignum pss_bn (n + 1)
        pss_lambda <- toBignum pss_bn 0
        pss_l2inv <- toBignum pss_bn 0

        paillierToSec pss_bn pss_p pss_q pss_n pss_n2 pss_g pss_lambda pss_l2inv

        pure PailSepSk{..}

    paheToPublic PailSepSk{..} =
        PailSepPk pss_simdn pss_bn pss_n pss_n_raw pss_n2 pss_g

    paheEnc PailSepPk{..} m = do
        let l = length m
        when (l /= psp_simdn) $ error "Paillier encrypt: length mismatch"
        fmap PailCiph $ forM [0..l-1] $ \i -> do
            r0 <- randomRIO (0, psp_n_raw - 1) `suchThat`
                     (\x -> gcd x psp_n_raw == 1)
            r <- toBignum psp_bn r0
            mi <- toBignum psp_bn $ m !! i
            c <- toBignum psp_bn 0
            paillierEnc psp_bn psp_n psp_n2 psp_g r mi c
            pure c

    paheDec PailSepSk{..} (PailCiph ms) = do
        let l = length ms
        when (l /= pss_simdn) $ error "Paillier decrypt: length mismatch"
        forM ms $ \ci -> do
            mi <- toBignum pss_bn 0
            paillierDec pss_bn pss_p pss_q pss_n pss_n2 pss_g pss_lambda pss_l2inv ci mi
            fromBignum pss_bn mi

    paheSIMDAdd PailSepPk{..} (PailCiph ms1) (PailCiph ms2) = do
        when (length ms1 /= psp_simdn || length ms2 /= psp_simdn) $
            error "Paillier simd add: length mismatch"
        fmap PailCiph $ forM (ms1 `zip` ms2) $ \(m1,m2) -> do
            mi <- toBignum psp_bn 0
            paillierHomAdd psp_bn psp_n psp_n2 m1 m2 mi
            pure mi

    paheSIMDMulScal PailSepPk{..} (PailCiph ms1) m2 = do
        when (length ms1 /= psp_simdn || length m2 /= psp_simdn) $
            error "Paillier simd mul: length mismatch"
        fmap PailCiph $ forM (ms1 `zip` m2) $ \(m1,p0) -> do
            mi <- toBignum psp_bn 0
            p <- toBignum psp_bn p0
            paillierHomMulScal psp_bn psp_n psp_n2 m1 p mi
            pure mi
