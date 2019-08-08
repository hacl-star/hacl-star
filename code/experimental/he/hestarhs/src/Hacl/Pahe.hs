{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies      #-}

-- | Class wrapper for packed AHE

module Hacl.Pahe where

import Universum

import qualified Data.ByteString as BS
import Data.List ((!!))
import System.Random (randomRIO)

import Hacl.Bignum
import qualified Hacl.Packing as P
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

    -- The number of elements we want to work over SIMD and their modulus
    paheKeyGen      :: Int -> Integer -> IO (PaheSk s)
    -- The length of vector inside
    paheK           :: PahePk s -> Int
    paheToPublic    :: PaheSk s -> PahePk s

    paheEnc         :: PahePk s -> [Integer] -> IO (PaheCiph s)
    paheDec         :: PaheSk s -> PaheCiph s -> IO [Integer]

    paheSIMDAdd     :: PahePk s -> PaheCiph s -> PaheCiph s -> IO (PaheCiph s)

    paheSIMDSub     :: PahePk s -> PaheCiph s -> PaheCiph s -> IO (PaheCiph s)
    default paheSIMDSub :: Pahe s => PahePk s -> PaheCiph s -> PaheCiph s -> IO (PaheCiph s)
    paheSIMDSub pk c1 c2 = paheSIMDAdd pk c1 =<< paheNeg pk c2


    paheSIMDMulScal :: PahePk s -> PaheCiph s -> [Integer] -> IO (PaheCiph s)

    paheMultBlind   :: PahePk s -> PaheCiph s -> IO (PaheCiph s)

    paheNeg         :: PahePk s -> PaheCiph s -> IO (PaheCiph s)
    default paheNeg :: Pahe s => PahePk s -> PaheCiph s -> IO (PaheCiph s)
    paheNeg pk ciph = paheSIMDMulScal pk ciph $ replicate (paheK pk) (-1)

    paheToBS        :: PahePk s -> PaheCiph s -> IO ByteString
    paheFromBS      :: PahePk s -> ByteString -> IO (PaheCiph s)


paheRerand :: Pahe s => PahePk s -> PaheCiph s -> IO (PaheCiph s)
paheRerand pk c = paheSIMDAdd pk c =<< paheEnc pk (replicate (paheK pk) 0)

----------------------------------------------------------------------------
-- GM
----------------------------------------------------------------------------

data GMSep

instance Pahe GMSep where
    data PaheCiph GMSep = GMCiph [Bignum]
    data PaheSk GMSep =
           GMSepSk { gms_simdn :: Int
                   , gms_bn :: Word32
                   , gms_p :: Bignum
                   , gms_pMin1 :: Bignum
                   , gms_pMin1Half :: Bignum
                   , gms_q :: Bignum
                   , gms_n :: Bignum
                   , gms_nRaw :: Integer
                   , gms_y :: Bignum
                   }
    data PahePk GMSep =
           GMSepPk { gmp_simdn :: Int
                   , gmp_bn :: Word32
                   , gmp_n :: Bignum
                   , gmp_nRaw :: Integer
                   , gmp_y :: Bignum
                   }


    paheKeyGen gms_simdn numsMod = do
        let roundUpPow2 x = 2 ^ log2 x
        (p,q,y,_,_,_) <- genDataGM $ max (roundUpPow2 $ log2 numsMod) 1024
        let n = p * q
        let gms_nRaw = n
        let gms_bn = fromIntegral $ length $ inbase b64 n

        gms_p <- toBignum gms_bn p
        gms_q <- toBignum gms_bn q
        gms_n <- toBignum gms_bn n
        gms_y <- toBignum gms_bn y

        gms_pMin1 <- toBignum gms_bn (p-1)
        gms_pMin1Half <- toBignum gms_bn ((p-1)`div`2)

        pure GMSepSk{..}

    paheK GMSepPk{..} = gmp_simdn

    paheToPublic GMSepSk{..} =
        GMSepPk {
            gmp_simdn = gms_simdn
          , gmp_bn    = gms_bn
          , gmp_n     = gms_n
          , gmp_nRaw = gms_nRaw
          , gmp_y     = gms_y }

    paheEnc GMSepPk{..} m = do
        when (length m /= gmp_simdn) $ error "GM encrypt: length mismatch"
        vals <- forM [0..gmp_simdn-1] $ \i -> do
            r0 <- randomRIO (0, gmp_nRaw - 1) `suchThat`
                     (\x -> gcd x gmp_nRaw == 1)
            r <- toBignum gmp_bn r0
            let mi = (== 1) . (`mod` 2) $ (m !! i)
            c <- toBignum gmp_bn 0
            gmEnc gmp_bn gmp_n gmp_y r mi c

            freeBignum r

            pure c
        pure $ GMCiph vals

    paheDec GMSepSk{..} (GMCiph ms) = do
        when (length ms /= gms_simdn) $ error "GM decrypt: length mismatch"
        fmap (map (bool 0 1)) $ forM ms $ gmDec gms_bn gms_p gms_pMin1 gms_pMin1Half

    paheSIMDAdd GMSepPk{..} (GMCiph ms1) (GMCiph ms2) = do
        when (length ms1 /= gmp_simdn || length ms2 /= gmp_simdn) $
            error "GMlier simd add: length mismatch"
        fmap GMCiph $ forM (ms1 `zip` ms2) $ \(m1,m2) -> do
            mi <- toBignum gmp_bn 0
            gmXor gmp_bn gmp_n m1 m2 mi
            pure mi

    paheSIMDSub pk m1 m2 = paheSIMDAdd pk m1 m2
    paheNeg pk m = paheSIMDAdd pk m =<< paheEnc pk (replicate (paheK pk) 1)

    paheSIMDMulScal GMSepPk{..} (GMCiph ms1) m2 = do
        when (length ms1 /= gmp_simdn || length m2 /= gmp_simdn) $
            error "GMlier simd mul: length mismatch"
        fmap GMCiph $ forM (ms1 `zip` m2) $ \(m1,p0) ->
            if (p0 `mod` 2) == 1 then pure m1 else do
                res <- toBignum gmp_bn 0
                gmXor gmp_bn gmp_n m1 m1 res
                pure res

    -- This function should "keep 0 as 0" and "make other values seem
    -- like random, but not zero". This is exactly ID for the GM.
    paheMultBlind _ ms = pure ms

    paheToBS GMSepPk{..} (GMCiph ms) = do
        when (length ms /= gmp_simdn) $ error "GM paheToBS failed length"
        fmap BS.concat $ forM ms $ fromBignumBS gmp_bn

    paheFromBS GMSepPk{..} bsl = do
        let parse bs = do
                let (a,b) = BS.splitAt (8 * fromIntegral gmp_bn) bs
                x <- toBignumBS gmp_bn a
                if BS.null b then pure [x] else do
                  y <- parse b
                  pure $ x : y
        fmap GMCiph $ parse bsl


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
                     , pss_nRaw :: Integer
                     , pss_n2 :: Bignum
                     , pss_g :: Bignum
                     , pss_lambda :: Bignum
                     , pss_l2inv :: Bignum
                     }
    data PahePk PailSep =
           PailSepPk { psp_simdn :: Int
                     , psp_bn :: Word32
                     , psp_n :: Bignum
                     , psp_nRaw :: Integer
                     , psp_n2 :: Bignum
                     , psp_g :: Bignum
                     }


    paheKeyGen pss_simdn numsMod = do
        let roundUpPow2 x = 2 ^ log2 x
        (p,q,_,_,_) <- genDataPaillier $ max (roundUpPow2 $ log2 numsMod) 1024
        let n = p * q
        let pss_nRaw = n
        let pss_bn = fromIntegral $ length $ inbase b64 (n*n)

        pss_p <- toBignum pss_bn p
        pss_q <- toBignum pss_bn q
        pss_n <- toBignum pss_bn n
        pss_n2 <- toBignum pss_bn (n * n)
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
          , psp_nRaw = pss_nRaw
          , psp_n2    = pss_n2
          , psp_g     = pss_g }

    paheEnc PailSepPk{..} m = do
        when (length m /= psp_simdn) $ error "Paillier encrypt: length mismatch"
        vals <- forM [0..psp_simdn-1] $ \i -> do
            r0 <- randomRIO (0, psp_nRaw - 1) `suchThat`
                     (\x -> gcd x psp_nRaw == 1)
            r <- toBignum psp_bn r0
            mi <- toBignum psp_bn $ (m !! i) `mod` psp_nRaw
            c <- toBignum psp_bn 0
            paillierEnc psp_bn psp_n psp_n2 psp_g r mi c

            mapM_ freeBignum [r,mi]

            pure c
        pure $ PailCiph vals

    paheDec PailSepSk{..} (PailCiph ms) = do
        let l = length ms
        when (l /= pss_simdn) $ error "Paillier decrypt: length mismatch"
        forM ms $ \ci -> do
            mi <- toBignum pss_bn 0
            paillierDec pss_bn pss_p pss_q pss_n pss_n2 pss_g pss_lambda pss_l2inv ci mi
            res <- fromBignum pss_bn mi
            freeBignum mi
            pure res

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
            p <- toBignum psp_bn $ p0 `mod` psp_nRaw
            paillierHomMulScal psp_bn psp_n psp_n2 m1 p mi
            freeBignum p
            pure mi

    paheMultBlind pk@PailSepPk{..} ms = do
        vals <- replicateM psp_simdn $ randomRIO (1,psp_nRaw`div`2)
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

----------------------------------------------------------------------------
-- DGK with CRT packing
----------------------------------------------------------------------------

data DgkCrt

instance Pahe DgkCrt where
    data PaheCiph DgkCrt = DgkCiph Bignum
    data PaheSk DgkCrt =
           DgkCrtSk { dcs_simdn :: Int
                    , dcs_bn :: Word32
                    , dcs_p :: Bignum
                    , dcs_q :: Bignum
                    , dcs_n :: Bignum
                    , dcs_nRaw :: Integer
                    , dcs_u :: Bignum
                    , dcs_uFactsPs :: BignumList
                    , dcs_uFactsEs :: BignumList
                    , dcs_uFactsLen :: Word32
                    , dcs_uFactsRaw :: [Integer]
                    , dcs_v :: Bignum
                    , dcs_g :: Bignum
                    , dcs_h :: Bignum
                    }
    data PahePk DgkCrt =
           DgkCrtPk { dcp_simdn :: Int
                    , dcp_bn :: Word32
                    , dcp_n :: Bignum
                    , dcp_nRaw :: Integer
                    , dcp_u :: Bignum
                    , dcp_uFactsRaw :: [Integer]
                    , dcp_g :: Bignum
                    , dcp_h :: Bignum
                    }


    paheKeyGen dcs_simdn numsMod = do
        let bits = 1024
        (dcs_uFactsRaw,p,q,u,v,g,h) <- dgkKeyGenWithLookup dcs_simdn numsMod bits
        let n = p * q
        let dcs_nRaw = n
        let dcs_bn = fromIntegral $ length $ inbase b64 (n*n)
        let dcs_uFactsLen = fromIntegral $ length dcs_uFactsRaw

        dcs_p <- toBignum dcs_bn p
        dcs_q <- toBignum dcs_bn q
        dcs_n <- toBignum dcs_bn n
        dcs_u <- toBignum dcs_bn u
        dcs_v <- toBignum dcs_bn v
        dcs_g <- toBignum dcs_bn g
        dcs_h <- toBignum dcs_bn h

        dcs_uFactsPs <- toBignumList dcs_bn dcs_uFactsRaw
        dcs_uFactsEs <- toBignumList dcs_bn $ replicate (length dcs_uFactsRaw) 1

        pure DgkCrtSk{..}

    paheK DgkCrtPk{..} = dcp_simdn

    paheToPublic DgkCrtSk{..} =
        DgkCrtPk {
            dcp_simdn = dcs_simdn
          , dcp_bn    = dcs_bn
          , dcp_n     = dcs_n
          , dcp_nRaw = dcs_nRaw
          , dcp_u     = dcs_u
          , dcp_uFactsRaw     = dcs_uFactsRaw
          , dcp_g     = dcs_g
          , dcp_h     = dcs_h
          }

    paheEnc DgkCrtPk{..} m = do
        when (length m /= dcp_simdn) $ error "DGK encrypt: length mismatch"

        r0 <- randomRIO (0, dcp_nRaw - 1) `suchThat`
                 (\x -> gcd x dcp_nRaw == 1)
        r <- toBignum dcp_bn r0
        mPacked <- toBignum dcp_bn $ P.crt dcp_uFactsRaw (P.crtToBase dcp_uFactsRaw m)
        c <- toBignum dcp_bn 0

        dgkEnc dcp_bn dcp_n dcp_u dcp_g dcp_h r mPacked c

        freeBignum r

        pure $ DgkCiph c

    paheDec DgkCrtSk{..} (DgkCiph cPacked) = do
        m <- toBignum dcs_bn 0
        dgkDec dcs_bn dcs_uFactsLen
            dcs_p dcs_q dcs_n dcs_u dcs_uFactsPs dcs_uFactsEs dcs_v dcs_g dcs_h cPacked m
        res <- fromBignum dcs_bn m
        freeBignum m
        pure $ P.crtInv dcs_uFactsRaw res

    paheSIMDAdd DgkCrtPk{..} (DgkCiph c1) (DgkCiph c2) = do
        c3 <- toBignum dcp_bn 0
        dgkHomAdd dcp_bn dcp_n c1 c2 c3
        pure $ DgkCiph c3

    paheSIMDMulScal DgkCrtPk{..} (DgkCiph c1) coeffs = do
        c3 <- toBignum dcp_bn 0
        bn_coeffs <- toBignum dcp_bn $ P.crt dcp_uFactsRaw (P.crtToBase dcp_uFactsRaw coeffs)
        dgkHomMulScal dcp_bn dcp_n c1 bn_coeffs c3
        freeBignum bn_coeffs
        pure $ DgkCiph c3

    paheMultBlind pk@DgkCrtPk{..} c = do
        scal <- replicateM dcp_simdn $ randomRIO (1, dcp_uFactsRaw !! 0 - 1)
        paheSIMDMulScal pk c scal

    paheToBS DgkCrtPk{..} (DgkCiph ms) = fromBignumBS dcp_bn ms

    paheFromBS DgkCrtPk{..} bsl = DgkCiph <$> toBignumBS dcp_bn bsl
