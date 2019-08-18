{-# LANGUAGE TypeFamilies #-}

-- | PAHE systems' implementaiton.

module Hacl.PaheImpl where

import Universum

import qualified Data.ByteString as BS
import Data.List (findIndex, (!!))
import qualified Data.List as L
import System.Random (randomRIO)

import Hacl.Bignum
import qualified Hacl.Packing as P
import Hacl.Pahe
import Hacl.Raw
import Hacl.Support
import Lib.Misc (suchThat)

import Utils


----------------------------------------------------------------------------
-- GM
----------------------------------------------------------------------------

data GMSep

gmEncOne :: Word32 -> Bignum -> Integer -> Bignum -> Integer -> IO Bignum
gmEncOne bn n nRaw y m = do
    r0 <- randomRIO (0, nRaw - 1) `suchThat`
             (\x -> gcd x nRaw == 1)
    r <- toBignum bn r0
    let mi = (== 1) . (`mod` 2) $ m
    c <- toBignum bn 0
    gmEnc bn n y r mi c

    freeBignum r
    pure c

gmEncRaw ::
       Int -> Word32 -> Bignum -> Integer -> Bignum -> [Integer] -> IO [Bignum]
gmEncRaw simdn bn n nRaw y ms = do
    when (length ms > simdn) $ error "GM encrypt: length mismatch"
    forM ms $ gmEncOne bn n nRaw y


instance Pahe GMSep where
    data PaheCiph GMSep = GMCiph { unGMCiph :: [Bignum] }
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
                   , gms_zero :: PaheCiph GMSep
                   , gms_one :: PaheCiph GMSep
                   }
    data PahePk GMSep =
           GMSepPk { gmp_simdn :: Int
                   , gmp_bn :: Word32
                   , gmp_n :: Bignum
                   , gmp_nRaw :: Integer
                   , gmp_y :: Bignum
                   , gmp_zero :: PaheCiph GMSep
                   , gmp_one :: PaheCiph GMSep
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


        gms_zero <-
            GMCiph <$>
            gmEncRaw gms_simdn gms_bn gms_n gms_nRaw gms_y (replicate gms_simdn 0)
        gms_one <-
            GMCiph <$>
            gmEncRaw gms_simdn gms_bn gms_n gms_nRaw gms_y (replicate gms_simdn 1)

        pure GMSepSk{..}

    paheK GMSepPk{..} = gmp_simdn

    paheToPlaintext GMSepPk{..} vals = map (`mod` 2) vals

    paheToPublic GMSepSk{..} = do
        GMSepPk {
            gmp_simdn = gms_simdn
          , gmp_bn    = gms_bn
          , gmp_n     = gms_n
          , gmp_nRaw = gms_nRaw
          , gmp_y     = gms_y
          , gmp_zero = gms_zero
          , gmp_one = gms_one
          }

    paheZero pk = gmp_zero pk
    paheOne pk = gmp_one pk
    paheMinOne = paheOne

    paheEnc GMSepPk{..} m =
        GMCiph <$> gmEncRaw gmp_simdn gmp_bn gmp_n gmp_nRaw gmp_y m

    paheDec GMSepSk{..} (GMCiph ms) = do
        when (length ms > gms_simdn) $ error "GM decrypt: length mismatch"
        decrypted <-
            fmap (map (bool 0 1)) $
            forM ms $ gmDec gms_bn gms_p gms_pMin1 gms_pMin1Half
        pure $ decrypted ++ replicate (gms_simdn - length ms) 0

    paheSIMDAdd GMSepPk{..} (GMCiph c1) (GMCiph c2) = do

        when (length c1 > gmp_simdn || length c2 > gmp_simdn) $
            error "GM simd add: length mismatch"

        let delta = case compare (length c1) (length c2) of
              EQ -> []
              LT -> drop (length c1) c2
              GT -> drop (length c2) c1

        commonSum <- forM (c1 `zip` c2) $ \(c1i,c2i) -> do
            ci <- toBignum gmp_bn 0
            gmXor gmp_bn gmp_n c1i c2i ci
            pure ci

        pure $ GMCiph $ commonSum ++ delta

    paheSIMDSub pk c1 c2 = paheSIMDAdd pk c1 c2
    paheNeg pk c@(GMCiph c') =
        paheSIMDAdd pk c =<< paheEnc pk (replicate (length c') 1)

    paheSIMDMulScal GMSepPk{..} (GMCiph c) scal = do
        when (length c > gmp_simdn || length scal > gmp_simdn) $
            error "GM simd mul: length mismatch"

        -- Only common length values are considered useful, others are
        -- zeroes anyway.
        fmap GMCiph $ forM (c `zip` scal) $ \(ci,s) ->
            if (s `mod` 2) == 1 then pure ci else do
                res <- toBignum gmp_bn 0
                gmXor gmp_bn gmp_n ci ci res
                pure res

    -- This function should "keep 0 as 0" and "make other values seem
    -- like random, but not zero". This is exactly ID for the GM.
    paheMultBlind _ ms = pure ms

    paheToBS GMSepPk{..} (GMCiph ms) = do
        when (length ms > gmp_simdn) $ error "GM paheToBS failed length"
        fmap BS.concat $ forM ms $ fromBignumBS gmp_bn

    paheFromBS GMSepPk{..} bsl = do
        let parse bs = do
                let (a,b) = BS.splitAt (8 * fromIntegral gmp_bn) bs
                x <- toBignumBS gmp_bn a
                if BS.null b then pure [x] else do
                  y <- parse b
                  pure $ x : y
        fmap GMCiph $ parse bsl

    pahePermute _ GMSepPk{..} (GMCiph c1) (GMCiph c2) perm = do
        unless (length perm == gmp_simdn * 2) $
            error "GM pahePermute permutation is too short"

        c1Tail <-
            replicateM (gmp_simdn - length c1) $
            gmEncOne gmp_bn gmp_n gmp_nRaw gmp_y 0
        c2Tail <-
            replicateM (gmp_simdn - length c2) $
            gmEncOne gmp_bn gmp_n gmp_nRaw gmp_y 0

        let cTot = c1 ++ c1Tail ++ c2 ++ c2Tail

        let permuted = map (\i -> cTot !! (perm !! i)) [0..gmp_simdn * 2 - 1]

        pure (GMCiph (take gmp_simdn permuted), GMCiph (drop gmp_simdn permuted))
    pahePermuteServ _ _ = pass
    pahePermuteHor _ _ _ = error "GM pahePermuteHor -- implement as in paillier"

----------------------------------------------------------------------------
-- Paillier
----------------------------------------------------------------------------

data PailSep

pailEncOne ::
       Word32 -> Bignum -> Integer -> Bignum -> Bignum -> Integer -> IO Bignum
pailEncOne bn n nRaw n2 g m = do
    r0 <- randomRIO (0, nRaw - 1) `suchThat`
             (\x -> gcd x nRaw == 1)
    r <- toBignum bn r0
    mi <- toBignum bn $ m `mod` nRaw
    c <- toBignum bn 0
    paillierEnc bn n n2 g r mi c

    mapM_ freeBignum [r,mi]

    pure c


pailEncRaw ::
       Int
    -> Word32
    -> Bignum
    -> Integer
    -> Bignum
    -> Bignum
    -> [Integer]
    -> IO [Bignum]
pailEncRaw simdn bn n nRaw n2 g ms = do
    when (length ms > simdn) $ error "Paillier encrypt: length mismatch"
    forM ms $ pailEncOne bn n nRaw n2 g

instance Pahe PailSep where
    data PaheCiph PailSep = PailCiph { unPailCiph :: [Bignum] }
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
                     , pss_zero :: PaheCiph PailSep
                     , pss_one :: PaheCiph PailSep
                     , pss_minOne :: PaheCiph PailSep
                     }
    data PahePk PailSep =
           PailSepPk { psp_simdn :: Int
                     , psp_bn :: Word32
                     , psp_n :: Bignum
                     , psp_nRaw :: Integer
                     , psp_n2 :: Bignum
                     , psp_g :: Bignum
                     , psp_zero :: PaheCiph PailSep
                     , psp_one :: PaheCiph PailSep
                     , psp_minOne :: PaheCiph PailSep

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

        pss_zero <-
            PailCiph <$>
            pailEncRaw pss_simdn pss_bn pss_n pss_nRaw pss_n2 pss_g (replicate pss_simdn 0)

        pss_one <-
            PailCiph <$>
            pailEncRaw pss_simdn pss_bn pss_n pss_nRaw pss_n2 pss_g (replicate pss_simdn 1)

        pss_minOne <-
            PailCiph <$>
            pailEncRaw pss_simdn pss_bn pss_n pss_nRaw pss_n2 pss_g (replicate pss_simdn (-1))

        pure PailSepSk{..}

    paheK PailSepPk{..} = psp_simdn

    paheToPlaintext PailSepPk{..} vals = map (`mod` psp_nRaw) vals

    paheToPublic PailSepSk{..} =
        PailSepPk {
            psp_simdn  = pss_simdn
          , psp_bn     = pss_bn
          , psp_n      = pss_n
          , psp_nRaw   = pss_nRaw
          , psp_n2     = pss_n2
          , psp_g      = pss_g
          , psp_zero   = pss_zero
          , psp_one    = pss_one
          , psp_minOne = pss_minOne
          }

    paheZero pk = psp_zero pk
    paheOne pk = psp_one pk
    paheMinOne pk = psp_minOne pk

    paheEnc PailSepPk{..} m =
        PailCiph <$> pailEncRaw psp_simdn psp_bn psp_n psp_nRaw psp_n2 psp_g m

    paheDec PailSepSk{..} (PailCiph cs) = do
        when (length cs > pss_simdn) $ error "Paillier decrypt: length mismatch"
        decrypted <- forM cs $ \ci -> do
            mi <- toBignum pss_bn 0
            paillierDec pss_bn pss_p pss_q pss_n pss_n2 pss_g pss_lambda pss_l2inv ci mi
            res <- fromBignum pss_bn mi
            freeBignum mi
            pure res
        pure $ decrypted ++ replicate (pss_simdn - length cs) 0

    paheSIMDAdd PailSepPk{..} (PailCiph c1) (PailCiph c2) = do
        when (length c1 > psp_simdn || length c2 > psp_simdn) $
            error "Paillier simd add: length mismatch"

        let delta = case compare (length c1) (length c2) of
              EQ -> []
              LT -> drop (length c1) c2
              GT -> drop (length c2) c1

        commonSum <- forM (c1 `zip` c2) $ \(c1i,c2i) -> do
            ci <- toBignum psp_bn 0
            paillierHomAdd psp_bn psp_n psp_n2 c1i c2i ci
            pure ci

        pure $ PailCiph $ commonSum ++ delta

    paheSIMDMulScal PailSepPk{..} (PailCiph c) scal = do
        when (length c > psp_simdn || length scal > psp_simdn) $
            error "Paillier simd mul: length mismatch"
        fmap PailCiph $ forM (c `zip` scal) $ \(ci,s) -> do
            cRes <- toBignum psp_bn 0
            sBn <- toBignum psp_bn $ s `mod` psp_nRaw
            paillierHomMulScal psp_bn psp_n psp_n2 ci sBn cRes
            freeBignum sBn
            pure cRes

    paheMultBlind pk@PailSepPk{..} c@(PailCiph cs) = do
        vals <- replicateM (length cs) $ randomRIO (1,psp_nRaw`div`2)
        paheSIMDMulScal pk c vals

    paheToBS PailSepPk{..} (PailCiph cs) = do
        when (length cs > psp_simdn) $
            error "Paillier paheToBS failed length"
        fmap BS.concat $ forM cs $ fromBignumBS psp_bn

    paheFromBS PailSepPk{..} bsl = do
        let parse bs = do
                let (a,b) = BS.splitAt (8 * fromIntegral psp_bn) bs
                x <- toBignumBS psp_bn a
                if BS.null b then pure [x] else do
                  y <- parse b
                  pure $ x : y
        fmap PailCiph $ parse bsl

    pahePermute _ PailSepPk{..} (PailCiph c1) (PailCiph c2) perm = do
        unless (length perm == psp_simdn * 2) $
            error "paillier pahePermute permutation is too short"

        c1Tail <-
            replicateM (psp_simdn - length c1) $
            pailEncOne psp_bn psp_n psp_nRaw psp_n2 psp_g 0
        c2Tail <-
            replicateM (psp_simdn - length c2) $
            pailEncOne psp_bn psp_n psp_nRaw psp_n2 psp_g 0

        let cTot = c1 ++ c1Tail ++ c2 ++ c2Tail

        let permuted = map (\i -> cTot !! (perm !! i)) [0..psp_simdn * 2 - 1]


        pure (PailCiph (take psp_simdn permuted), PailCiph (drop psp_simdn permuted))
    pahePermuteServ _ _ = pass
    pahePermuteHor _ ciphs perms = do
        let permsM = length $ perms !! 0
        let permsinv = map (\p -> map (\i -> fromMaybe (error"pahePermuteServ") $
                                       findIndex (==i) p)
                                      [0..permsM-1]) perms
        let rows :: [[Bignum]]
                = map (\(perm,row) ->
                         map (\pIx -> unPailCiph (ciphs !! pIx) !! row) perm)
                      (permsinv `zip` [0..])
        pure $ map PailCiph $ L.transpose rows

----------------------------------------------------------------------------
-- DGK with CRT packing
----------------------------------------------------------------------------

data DgkCrt

{-# INLINE dgkEncRaw #-}
dgkEncRaw ::
       Int
    -> Word32
    -> Bignum
    -> Integer
    -> Bignum
    -> [Integer]
    -> [Integer]
    -> Bignum
    -> Bignum
    -> [Integer]
    -> IO Bignum
dgkEncRaw simdn bn n nRaw u uFactsRaw uFactsTailProd g h ms = do
    when (length ms > simdn) $ error "DGK encrypt: length mismatch"

    r0 <- randomRIO (0, nRaw - 1) -- `suchThat` (\x -> gcd x nRaw == 1)
    r <- toBignum bn r0
    mPacked <- toBignum bn $ P.crt uFactsRaw uFactsTailProd ms -- (P.crtToBase uFactsRaw ms)
    c <- toBignum bn 0

    dgkEnc bn n u g h r mPacked c

    freeBignum r
    freeBignum mPacked

    pure c


instance Pahe DgkCrt where
    data PaheCiph DgkCrt = DgkCiph Word8 Bignum deriving (Generic)
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
                    , dcs_uFactsRawTProds :: [Integer]
                    , dcs_v :: Bignum
                    , dcs_g :: Bignum
                    , dcs_h :: Bignum
                    , dcs_zero :: PaheCiph DgkCrt
                    , dcs_one :: PaheCiph DgkCrt
                    , dcs_minOne :: PaheCiph DgkCrt
                    , dcs_vbis :: [Bignum]
                    , dcs_tmp :: Bignum
                    }
           deriving (Generic)
    data PahePk DgkCrt =
           DgkCrtPk { dcp_simdn :: Int
                    , dcp_bn :: Word32
                    , dcp_n :: Bignum
                    , dcp_nRaw :: Integer
                    , dcp_u :: Bignum
                    , dcp_uFactsPs :: BignumList
                    , dcp_uFactsEs :: BignumList
                    , dcp_uFactsRaw :: [Integer]
                    , dcp_uFactsRawTProds :: [Integer]
                    , dcp_g :: Bignum
                    , dcp_h :: Bignum
                    , dcp_zero :: PaheCiph DgkCrt
                    , dcp_one :: PaheCiph DgkCrt
                    , dcp_minOne :: PaheCiph DgkCrt
                    , dcp_tmp :: Bignum
                    }
           deriving (Generic)


    paheKeyGen dcs_simdn numsMod = do
        when (dcs_simdn > 255) $ error "dgk simdn can't be greater than 255"
        let bits = 1024
        (dcs_uFactsRaw,p,q,u,v,g,h) <- dgkKeyGenWithLookup dcs_simdn numsMod bits
        let n = p * q
        let dcs_nRaw = n
        let dcs_bn = fromIntegral $ length $ inbase b64 (n*n)
        let dcs_uFactsLen = fromIntegral $ length dcs_uFactsRaw
        let dcs_uFactsRawTProds = P.compTailProds dcs_uFactsRaw

        dcs_p <- toBignum dcs_bn p
        dcs_q <- toBignum dcs_bn q
        dcs_n <- toBignum dcs_bn n
        dcs_u <- toBignum dcs_bn u
        dcs_v <- toBignum dcs_bn v
        dcs_g <- toBignum dcs_bn g
        dcs_h <- toBignum dcs_bn h

        dcs_uFactsPs <- toBignumList dcs_bn dcs_simdn dcs_uFactsRaw
        dcs_uFactsEs <- toBignumList dcs_bn dcs_simdn $ replicate (length dcs_uFactsRaw) 1

        dcs_zero <- DgkCiph (fromIntegral dcs_simdn) <$>
            dgkEncRaw dcs_simdn dcs_bn dcs_n dcs_nRaw dcs_u dcs_uFactsRaw
            dcs_uFactsRawTProds dcs_g dcs_h
            (replicate dcs_simdn 0)

        dcs_one <- DgkCiph (fromIntegral dcs_simdn) <$>
            dgkEncRaw dcs_simdn dcs_bn dcs_n dcs_nRaw dcs_u dcs_uFactsRaw
            dcs_uFactsRawTProds dcs_g dcs_h
            (replicate dcs_simdn 1)

        dcs_minOne <- DgkCiph (fromIntegral dcs_simdn) <$>
            dgkEncRaw dcs_simdn dcs_bn dcs_n dcs_nRaw dcs_u dcs_uFactsRaw
            dcs_uFactsRawTProds dcs_g dcs_h
            (replicate dcs_simdn (-1))

        dcs_vbis <-
            mapM (toBignum dcs_bn) $
            map ((product dcs_uFactsRaw * v) `div`) dcs_uFactsRaw

        dcs_tmp <- toBignum dcs_bn 0

        pure DgkCrtSk{..}

    paheK DgkCrtPk{..} = dcp_simdn

    paheToPlaintext DgkCrtPk{..} vals = P.crtToBase dcp_uFactsRaw vals

    paheToPublic DgkCrtSk{..} =
        DgkCrtPk {
            dcp_simdn = dcs_simdn
          , dcp_bn    = dcs_bn
          , dcp_n     = dcs_n
          , dcp_nRaw = dcs_nRaw
          , dcp_u     = dcs_u
          , dcp_uFactsPs = dcs_uFactsPs
          , dcp_uFactsEs = dcs_uFactsEs
          , dcp_uFactsRaw     = dcs_uFactsRaw
          , dcp_uFactsRawTProds = dcs_uFactsRawTProds
          , dcp_g     = dcs_g
          , dcp_h     = dcs_h
          , dcp_zero   = dcs_zero
          , dcp_one    = dcs_one
          , dcp_minOne = dcs_minOne
          , dcp_tmp = dcs_tmp
          }

    paheZero pk = dcp_zero pk
    paheOne pk = dcp_one pk
    paheMinOne pk = dcp_minOne pk

    paheEnc DgkCrtPk{..} m =
        DgkCiph (fromIntegral $ length m) <$>
        dgkEncRaw dcp_simdn dcp_bn dcp_n dcp_nRaw dcp_u dcp_uFactsRaw
        dcp_uFactsRawTProds dcp_g dcp_h m

    paheDec DgkCrtSk{..} (DgkCiph _ cPacked) = do
        dgkDec dcs_bn dcs_uFactsLen
            dcs_p dcs_q dcs_n dcs_u dcs_uFactsPs dcs_uFactsEs dcs_v dcs_g dcs_h cPacked dcs_tmp
        res <- fromBignum dcs_bn dcs_tmp
        pure $ P.crtInv dcs_uFactsRaw res

    paheNeg pk ciph@(DgkCiph len _) =
        paheSIMDMulScal pk ciph $ replicate (fromIntegral len) (-1)

    paheSIMDAdd DgkCrtPk{..} (DgkCiph prefLen1 c1) (DgkCiph prefLen2 c2) = do
        c3 <- toBignum dcp_bn 0
        dgkHomAdd dcp_bn dcp_n c1 c2 c3
        pure $ DgkCiph (max prefLen1 prefLen2) c3

    paheSIMDMulScal DgkCrtPk{..} (DgkCiph prefLen c1) scal = do
        --when (length scal > dcp_simdn) $
        --    error "Paillier simd mul: length mismatch"

        c3 <- toBignumZero dcp_bn
        bn_coeffs <-
            toBignum dcp_bn $
            P.crt dcp_uFactsRaw dcp_uFactsRawTProds scal

        dgkHomMulScal dcp_bn dcp_n c1 bn_coeffs c3
        freeBignum bn_coeffs
        pure $ DgkCiph (min prefLen (fromIntegral $ length scal)) c3

    paheMultBlind pk@DgkCrtPk{..} c = do
        scal <- replicateM dcp_simdn $ randomRIO (1, dcp_uFactsRaw !! 0 - 1)
        paheSIMDMulScal pk c scal

    paheIsZero DgkCrtSk{..} (DgkCiph prefixN ciph) = do
        res <- forM (take (fromIntegral prefixN) dcs_vbis) $ \vBi -> do
            bnModExp dcs_bn dcs_bn dcs_n ciph vBi dcs_tmp
            bnIsOne dcs_bn dcs_tmp
        pure res --  ++ replicate (dcs_simdn - fromIntegral prefixN) False

    paheToBS DgkCrtPk{..} (DgkCiph prefLen ms) = BS.cons prefLen <$> fromBignumBS dcp_bn ms

    paheFromBS DgkCrtPk{..} bsl =
        let (a,b) = fromMaybe (error "paheFromBS dgk failed") $ BS.uncons bsl in
        DgkCiph a <$> toBignumBS dcp_bn b

    pahePermute = error "DGK pahePermute -- implement using PermuteFold"
    pahePermuteServ = error "DGK pahePermute -- implement using PermuteFold"
    pahePermuteHor _ _ _ = error "DGK permuteHor -- implement as in DGK comp"

instance NFData (PaheCiph DgkCrt)
instance NFData (PaheSk DgkCrt)
instance NFData (PahePk DgkCrt)
