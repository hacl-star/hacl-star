{-# LANGUAGE TypeFamilies #-}

-- | Class wrapper for packed AHE

module Hacl.Pahe where

import Universum

import qualified Data.ByteString as BS
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
    -- The length of vector inside
    paheK           :: PahePk s -> Int
    paheToPublic    :: PaheSk s -> PahePk s

    paheEnc         :: PahePk s -> [Integer] -> IO (PaheCiph s)
    paheDec         :: PaheSk s -> PaheCiph s -> IO [Integer]

    paheSIMDAdd     :: PahePk s -> PaheCiph s -> PaheCiph s -> IO (PaheCiph s)
    paheSIMDMulScal :: PahePk s -> PaheCiph s -> [Integer] -> IO (PaheCiph s)
    paheMultBlind   :: PahePk s -> PaheCiph s -> IO (PaheCiph s)

    paheToBS        :: PahePk s -> PaheCiph s -> IO ByteString
    paheFromBS      :: PahePk s -> ByteString -> IO (PaheCiph s)

paheNeg :: Pahe s => PahePk s -> PaheCiph s -> IO (PaheCiph s)
paheNeg pk ciph = paheSIMDMulScal pk ciph $ replicate (paheK pk) (-1)

paheSIMDSub :: Pahe s => PahePk s -> PaheCiph s -> PaheCiph s -> IO (PaheCiph s)
paheSIMDSub pk c1 c2 = paheSIMDAdd pk c1 =<< paheNeg pk c2

paheRerand :: Pahe s => PahePk s -> PaheCiph s -> IO (PaheCiph s)
paheRerand pk c = paheSIMDAdd pk c =<< paheEnc pk (replicate (paheK pk) 0)

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

    paheK PailSepPk{..} = psp_simdn

    paheToPublic PailSepSk{..} =
        PailSepPk {
            psp_simdn = pss_simdn
          , psp_bn    = pss_bn
          , psp_n     = pss_n
          , psp_n_raw = pss_n_raw
          , psp_n2    = pss_n2
          , psp_g     = pss_g }

    paheEnc PailSepPk{..} m = do
        when (length m /= psp_simdn) $ error "Paillier encrypt: length mismatch"
        vals <- forM [0..psp_simdn-1] $ \i -> do
            r0 <- randomRIO (0, psp_n_raw - 1) `suchThat`
                     (\x -> gcd x psp_n_raw == 1)
            r <- toBignum psp_bn r0
            mi <- toBignum psp_bn $ (m !! i) `mod` psp_n_raw
            c <- toBignum psp_bn 0
            paillierEnc psp_bn psp_n psp_n2 psp_g r mi c

            pure c
        pure $ PailCiph vals

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
            p <- toBignum psp_bn $ p0 `mod` psp_n_raw
            paillierHomMulScal psp_bn psp_n psp_n2 m1 p mi
            pure mi

    paheMultBlind pk@PailSepPk{..} ms = do
        vals <- replicateM psp_simdn $ randomRIO (0,psp_n_raw-1)
        paheSIMDMulScal pk ms vals

    paheToBS PailSepPk{..} (PailCiph ms) = do
        when (length ms /= psp_simdn) $
            error "Paillier paheToBS failed length"
        fmap BS.concat $ forM ms $ fromBignumBS psp_bn

    paheFromBS PailSepPk{..} bsl = do
        let parse bs = do
                let (a,b) = BS.splitAt (8 * fromIntegral psp_bn) bs
                x <- toBignumBS psp_bn a
                if BS.null b then pure [x] else do
                  y <- parse b
                  pure $ x : y
        fmap PailCiph $ parse bsl
