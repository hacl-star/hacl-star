-- | Implementation of argmax protocol

module Argmax where

import Universum

import Control.Concurrent.Async (concurrently)
import qualified Data.ByteString as BS
import Data.List (findIndex, (!!))
import qualified Data.List.NonEmpty as NE
import System.Random (randomRIO)
import System.ZMQ4

import Comparison
import Hacl
import Utils



w64ToBs :: Word64 -> ByteString
w64ToBs = BS.pack . map fromIntegral . inbase 256 . fromIntegral

w64FromBs :: ByteString -> Word64
w64FromBs = fromIntegral . frombase 256 . map fromIntegral . BS.unpack

----------------------------------------------------------------------------
-- Argmax #0
----------------------------------------------------------------------------

argmaxClient ::
       (Pahe sTop, Pahe sDGK, Pahe sGM)
    => Socket Req
    -> PahePk sTop
    -> PahePk sDGK
    -> PahePk sGM
    -> Int
    -> Int
    -> [PaheCiph sTop]
    -> IO (PaheCiph sTop, [Word64])
argmaxClient sock pkTop pkDGK pkGM l r vals = do
    let k = paheK pkTop
    let m = length vals
    perms <- replicateM r $ shuffle [0..m-1]
    let permsInv =
            map (\p -> map (\i -> fromMaybe (error"perminv argmax") $
                                   findIndex (==i) p)
                                  [0..r-1]) perms

    log $ "Perm: " <> show perms
    valsPerm <- pahePermuteHor pkTop vals perms

    let loop curMax i = if i == m then pure curMax else do
            log $ "Client loop index " <> show i
            bi <-
                measureTimeSingle "Client argmax SC" $
                secureCompareClient sock pkTop pkDGK pkGM l r
                (valsPerm !! i) curMax
            ri <- replicateM r $ randomRIO (0, 2^(l + lambda) - 1)
            si <- replicateM r $ randomRIO (0, 2^(l + lambda) - 1)
            mMasked <- paheSIMDAdd pkTop curMax =<< paheEnc pkTop ri
            aMasked <- paheSIMDAdd pkTop (valsPerm !! i) =<< paheEnc pkTop si

            biBS <- paheToBS pkGM bi
            toSend <- (biBS :) <$> mapM (paheToBS pkTop) [mMasked, aMasked]
            sendMulti sock $ NE.fromList toSend

            [biTop,vi] <- mapM (paheFromBS pkTop) =<< receiveMulti sock
            newMax <- do
                biTopNeg <- paheSIMDSub pkTop biTop (paheOne pkTop)
                tmp1 <- paheSIMDMulScal pkTop biTopNeg ri
                tmp2 <- paheSIMDMulScal pkTop biTop si
                tmp3 <- paheSIMDAdd pkTop vi tmp1
                paheSIMDSub pkTop tmp3 tmp2

            loop newMax (i+1)

    maxval <- loop (valsPerm !! 0) 1
    log "Client: argmax loop ended"

    send sock [] ""
    indices <- map w64FromBs <$> receiveMulti sock

    let indices' = map (\(resI,permI) ->
                          fromIntegral $ (permsInv !! permI) !! (fromIntegral resI))
                       (indices `zip` [0..])

    pure (maxval, indices')

argmaxServer ::
       (Pahe sTop, Pahe sDGK, Pahe sGM)
    => Socket Rep
    -> PaheSk sTop
    -> PaheSk sDGK
    -> PaheSk sGM
    -> Int
    -> Int
    -> Int
    -> IO ()
argmaxServer sock skTop skDGK skGM l m r = do
    let pkTop = paheToPublic skTop
    let pkGM = paheToPublic skGM
    let k = paheK pkTop

    let loop ixs i = if i == m then pure ixs else do
            log $ "Server loop ixs " <> show i
            secureCompareServer sock skTop skDGK skGM l r
            [bsBi,bsM,bsA] <- receiveMulti sock
            [mMasked,aMasked] <- mapM (paheFromBS pkTop) [bsM,bsA]
            log $ "Server loop: got values from client"
            bi <- paheDec skGM =<< paheFromBS pkGM bsBi
            let biNeg = map (\x -> 1 - x) bi

            vi <- do
                -- bi * ai + (1-bi) * mi
                tmp1 <- paheSIMDMulScal pkTop aMasked bi
                tmp2 <- paheSIMDMulScal pkTop mMasked biNeg
                paheSIMDAdd pkTop tmp1 tmp2

            reencBi <- paheEnc pkTop bi
            sendMulti sock =<< NE.fromList <$> mapM (paheToBS pkTop) [reencBi,vi]

            let ixs' =
                    map (\j -> if bi !! j == 1 then i else ixs !! j) [0..k-1]
            log "Server loop end"
            loop ixs' (i+1)

    indices <- loop (replicate k 0) 1
    log $ "Server: argmax loop ended, indices: " <> show indices

    _ <- receive sock
    sendMulti sock $ NE.fromList $ map (w64ToBs . fromIntegral) indices

    log "Server: exiting"

------------------------------------------------------------------------------
---- Log argmax
--------------------------------------------------------------------------------


-- TODO we're missing the full power of the system because the first
-- comparison uses 2^(m-1) slots only.
argmaxLog2Client ::
       (Pahe sTop, Pahe sDGK, Pahe sGM)
    => Socket Req
    -> PahePk sTop
    -> PahePk sDGK
    -> PahePk sGM
    -> Int
    -> Int
    -> PaheCiph sTop
    -> PaheCiph sTop
    -> IO Int
argmaxLog2Client sock pkTop pkDGK pkGM l m v1 v2 = do
    let k = paheK pkTop
    when (2^m > k) $ error "argmaxLogClient m is too big"
    when (odd k) $ error "k must be even, ideally a power of 2"

    perm <- shuffle [0..2*k-1]
    log $ "Client: perm " <> show perm
    let perminv j = fromMaybe (error "argmaxLogCli perminv") $ findIndex (==j) perm
    (v1Perm,v2Perm) <-
        measureTimeSingle "perm" $ pahePermute sock pkTop v1 v2 perm
    log "Client: perm done"

    -- p1 and p2 are of length 2^i each
    let loop p1 p2 i = do
            log $ "Client loop index " <> show i
            let curLen = 2^i
            -- delta is p2 <= p1
            delta <- secureCompareClient sock pkTop pkDGK pkGM l (2^i) p1 p2
            -- we only care about first 2^(i-1) bits of this mask though
            p1mask <- replicateM curLen $ randomRIO (0, 2 ^ l - 1)
            p2mask <- replicateM curLen $ randomRIO (0, 2 ^ l - 1)
            p1masked <- paheSIMDAdd pkTop p1 =<< paheEnc pkTop p1mask
            p2masked <- paheSIMDAdd pkTop p2 =<< paheEnc pkTop p2mask

            pXMaskedBS <- mapM (paheToBS pkTop) [p1masked,p2masked]
            deltaBS <- paheToBS pkGM delta
            sendMulti sock $ NE.fromList (deltaBS:pXMaskedBS)

            let p1maskNeg = map negate p1mask
            let p2maskNeg = map negate p2mask

            when (i > 0) $ do
                -- each of these is of size 2^(i-1)
                [delta1,delta2,combM1,combM2] <-
                    mapM (paheFromBS pkTop) =<< receiveMulti sock


                (comb1,comb2) <- measureTimeSingle "argmax log2 client combine" $ do
                  delta1Neg <- paheSIMDSub pkTop (paheOne pkTop) delta1
                  delta2Neg <- paheSIMDSub pkTop (paheOne pkTop) delta2

                  let nextLen = curLen`div`2
                  let getlow xs = take nextLen xs
                  let gethigh xs = take nextLen (drop nextLen xs)
                  -- unmask by doing combinedMasked - delta*p1 - deltaNeg*p2
                  comb1 <- do
                      tmp1 <- paheSIMDMulScal pkTop delta1 $ getlow p1maskNeg
                      tmp2 <- paheSIMDMulScal pkTop delta1Neg $ getlow p2maskNeg
                      paheSIMDAdd pkTop combM1 =<< paheSIMDAdd pkTop tmp1 tmp2

                  comb2 <- do
                      tmp1 <- paheSIMDMulScal pkTop delta2 $ gethigh p1maskNeg
                      tmp2 <- paheSIMDMulScal pkTop delta2Neg $ gethigh p2maskNeg
                      paheSIMDAdd pkTop combM2 =<< paheSIMDAdd pkTop tmp1 tmp2
                  pure (comb1,comb2)
                loop comb1 comb2 (i-1)

    loop v1Perm v2Perm m

    maxIndex <- fromIntegral . w64FromBs <$> receive sock

    pure $ perm !! maxIndex

argmaxLog2Server ::
       (Pahe sTop, Pahe sDGK, Pahe sGM)
    => Socket Rep
    -> PaheSk sTop
    -> PaheSk sDGK
    -> PaheSk sGM
    -> Int
    -> Int
    -> IO ()
argmaxLog2Server sock skTop skDGK skGM l m = do
    let pkTop = paheToPublic skTop
    let pkGM = paheToPublic skGM

    pahePermuteServ sock skTop

    -- at step i we're comparing two arrays of size 2^i each
    -- so the first step has index m-1
    let loop (ixs::[Integer]) i = do
            log $ "Server loop index " <> show i
            secureCompareServer sock skTop skDGK skGM l (2^i)

            let curLen = 2^i

            [deltaBS,p1bs,p2bs] <- receiveMulti sock
            delta <- (fmap (map (bool 1 0)) . paheIsZero skGM) =<<
                paheFromBS pkGM deltaBS
            [p1,p2] <-
                mapM (paheDec skTop <=< paheFromBS pkTop) [p1bs,p2bs]
            let pCombined = simdadd (simdmul p1 delta)
                                    (simdmul p2 (map (\x -> 1 - x) delta))
            log $ "Server, delta: " <> show delta
            let ixs' =
                    let delta' = take curLen delta in
                    let (ixs0, ixs1) = splitAt curLen ixs in
                    simdadd (simdmul ixs0 delta')
                            (simdmul ixs1 (map (\x -> 1 - x) delta'))
            log $ "Server, ixs': " <> show ixs'

            if i == 0 then pure ixs' else do
                let nextLen = 2^(i-1)
                let getlow xs = take nextLen xs
                let gethigh xs = take nextLen (drop nextLen xs)

                let delta1 = getlow delta
                let delta2 = gethigh delta
                let pComb1 = getlow pCombined
                let pComb2 = gethigh pCombined
                sendMulti sock =<<
                    NE.fromList <$>
                    mapM (paheToBS pkTop <=< paheEnc pkTop) [delta1,delta2,pComb1,pComb2]
                loop ixs' (i-1)

    ixs <- loop [0..2^(m+1)] m
    let maxIx = ixs !! 0
    log $ "Server: argmax loop ended, indices: " <> show maxIx

    send sock [] $ w64ToBs $ fromIntegral maxIx

    log "Server: exiting"




----------------------------------------------------------------------------
-- Runner
----------------------------------------------------------------------------

-- Baseline: linear argmax takes 3.66 seconds w/o networking
-- to compare 32 numbers of 64 bits. More like 2.73 sec?
--
-- Log argmax: k = 16, comparing 32 numbers: 1.25 sec with shuffling
-- Without heavy shuffing: 1.17?
--
--
-- LAN usb:
-- Log argmax k = 16, 32 numbers of 64 bits: 1.4s
-- Linear argmax: k = 1, r = 1, 4.18s
--
-- WAN delay 51.6 ms:
-- Linear argmax: 13.67
-- Log argmax: 3.064

_testArgmax :: Socket Req -> Socket Rep -> IO ()
_testArgmax req rep = do
    putTextLn "Initialised the context, generating params"

    putTextLn "Keygen..."
    -- SIMD parameter
    let k = 16
    -- bit size of numbers we compare
    let l = 64
    -- plaintext space size
    --let margin = 2^(lambda + l)
    let margin = 2^(l+3)

    -- system used to carry long secureCompare results
    skTop <- paheKeyGen @PailSep k (2^(lambda + l + 100))
    --let skTop = skDGK
    let pkTop = paheToPublic skTop

    -- system used for DGK comparison
    --skDGK <- paheKeyGen @PailSep k (2^(lambda+l))
    skDGK <- paheKeyGen @DgkCrt k (5 + 3 * fromIntegral l)
    let pkDGK = paheToPublic skDGK

    -- system used to carry QR results
    skGM <- paheKeyGen @GMSep k margin
    --skGM <- paheKeyGen @DgkCrt k margin
    --let skGM = skDGK
    let pkGM = paheToPublic skGM


    let testLogArgmax = do
          -- Number of argmax input elements
          let m::Int = 2 ^ (log2 (fromIntegral k) - 1 :: Integer)
          --let m::Int = 20
          let mlog::Int = log2 (m-1)

          v1 <- replicateM k $ randomRIO (0,2^l-1)
          v2 <- replicateM k $ randomRIO (0,2^l-1)
          let vals = v1 ++ v2
          putTextLn $ "Values for argmax: " <> show vals
          let expectedMax = foldr1 max vals
          e1 <- paheEnc pkTop v1
          e2 <- paheEnc pkTop v2

          ((ix,()),timing) <-
              measureTimeRet $
              concurrently
              (argmaxLog2Client req pkTop pkDGK pkGM l mlog e1 e2)
              (argmaxLog2Server rep skTop skDGK skGM l mlog)

          unless (vals !! ix == expectedMax) $ do
              putTextLn $ "vals: " <> show vals
              error $ "logArgmax broken, ix: " <> show ix
          pure timing

--    let testPermFold = do
--          perm <- shuffle [0..2*k-1]
--          putTextLn $ "perm " <> show perm
--
--          f1 <- replicateM k $ randomRIO (0,2^l-1)
--          f2 <- replicateM k $ randomRIO (0,2^l-1)
--          putTextLn $ "Elements to shufle: " <> show (f1,f2)
--          f1Enc <- paheEnc pkTop f1
--          f2Enc <- paheEnc pkTop f2
--
--          ((v1,v2),()) <-
--              concurrently
--              (permuteFoldClient req pkTop l perm f1Enc f2Enc)
--              (permuteFoldServer rep skTop)
--
--          print =<< paheDec skTop v1
--          print =<< paheDec skTop v2
--
--    let testPerm = do
--          perm <- shuffle [0..k-1]
--          putTextLn $ "perm " <> show perm
--
--          f <- replicateM k $ randomRIO (0,2^l-1)
--          print f
--          fEnc <- paheEnc pkTop f
--
--          (valsPerm,()) <-
--              concurrently
--              (permuteClient req pkTop l perm fEnc)
--              (permuteServer rep skTop)
--
--          valsDec <- paheDec skTop valsPerm
--          print valsDec

    let testArgmax m r = do
            putTextLn "Starting argmax"
            vals <- replicateM m $ replicateM r $ randomRIO (0,2^l-1)
            --print vals
            let expectedMaxs = foldr1 (\l1 l2 -> map (uncurry max) $ zip l1 l2) vals
            encVals <- mapM (paheEnc pkTop) vals
            putTextLn "Launching"

            (((maxes,indices),()),timing) <-
                measureTimeRet $
                concurrently
                (argmaxClient req pkTop pkDGK pkGM l r encVals)
                (argmaxServer rep skTop skDGK skGM l m r)

            putTextLn "Maxes/indices"
            decMaxes <- paheDec skTop maxes

            unless (expectedMaxs `isPrefixOf` decMaxes) $ do
                print expectedMaxs
                print decMaxes
                print indices
                error "Argmax failed"

            putTextLn "OK"
            pure timing

    timings <- replicateM 10 $ testLogArgmax
    --timings <- replicateM 10 $ testArgmax 32 1
    print $ average timings

--    --testLogArgmax
--    let average xs = foldr1 (+) xs `div` (fromIntegral $ length xs)
--    timings <- replicateM 10  testLogArgmax
--    --timings <- replicateM 10 $ testArgmax 1
--    print $ average timings

    --testPermFold
    --testPerm
    --testFold
