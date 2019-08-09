-- | Implementation of argmax protocol

module Argmax where

import Universum

import Control.Concurrent.Async (concurrently)
import Data.Array.IO
import Data.Bits (testBit)
import qualified Data.ByteString as BS
import Data.List (findIndex, (!!))
import qualified Data.List.NonEmpty as NE
import System.Random (randomRIO)
import System.ZMQ4

import Hacl
import Utils



lambda :: Integral a => a
lambda = 80

w64ToBs :: Word64 -> ByteString
w64ToBs = BS.pack . map fromIntegral . inbase 256 . fromIntegral

w64FromBs :: ByteString -> Word64
w64FromBs = fromIntegral . frombase 256 . map fromIntegral . BS.unpack

----------------------------------------------------------------------------
-- DGK
----------------------------------------------------------------------------

-- taken from https://wiki.haskell.org/Random_shuffle
shuffle :: [a] -> IO [a]
shuffle xs = do
        ar <- newArray' n xs
        forM [1..n] $ \i -> do
            j <- randomRIO (i,n)
            vi <- readArray ar i
            vj <- readArray ar j
            writeArray ar j vi
            return vj
  where
    n = length xs
    newArray' :: Int -> [a] -> IO (IOArray Int a)
    newArray' n' xs' =  newListArray (1,n') xs'


-- | Compute r <= c jointly. Client has r, server has c.
dgkClient ::
       (Pahe sDGK, Pahe sGM)
    => Socket Req
    -> PahePk sDGK
    -> PahePk sGM
    -> Int
    -> [Integer]
    -> IO (PaheCiph sGM)
dgkClient sock pkDGK pkGM l rs = do

    let k = paheK pkDGK -- they should be similar between two schemes
    log "Client: dgk started"
    send sock [] "init"

    let rbits = map (\i -> map (\c -> bool 0 1 $ testBit c i) rs) [0..l-1]
    --log $ "Client rbits: " <> show rbits
    encRBits <- mapM (paheEnc pkDGK) rbits

    cs <- mapM (paheFromBS pkDGK) =<< receiveMulti sock


    log "Client: computing xors"
    xors <- forM (cs `zip` [0..]) $ \(ci,i) -> do
        let bitmask = rbits !! i
        let bitmaskNeg = map (\x -> 1 - x) bitmask

        -- ci * maskNeg + (1-ci) * mask
        a <- paheSIMDMulScal pkDGK ci bitmaskNeg
        oneMinCi <- paheSIMDSub pkDGK (paheOne pkDGK) ci
        c <- paheSIMDMulScal pkDGK oneMinCi bitmask
        paheSIMDAdd pkDGK a c

    --log "XORS: "
    -- print =<< mapM (paheDec skDGK) xors

    delta <- replicateM k (randomRIO (0,1))
    deltaEnc <- paheEnc pkDGK delta
    let s0 = map (\i -> 1 - 2 * i) delta
    log $ "Client: s = " <> show s0
    s <- paheEnc pkDGK s0

    let computeXorSums i prev = do
            nextXorSum <- paheSIMDAdd pkDGK prev (xors !! i)
            xorsTail <- if i == 0 then pure [] else computeXorSums (i-1) nextXorSum
            pure $ nextXorSum : xorsTail
    xorsums <- reverse <$> computeXorSums (l-1) (paheZero pkDGK)

    -- log "XOR SUBS: "
    -- print =<< mapM (paheDec skDGK) xorsums

    log "Client: computing cis"
    ci <- forM [0..l-1] $ \i -> do
        a <- paheSIMDAdd pkDGK s (encRBits !! i)
        b <- paheSIMDSub pkDGK a (cs !! i)

        if i == l-1 then pure b else do
            xorsum3 <- paheSIMDMulScal pkDGK (xorsums !! (i+1)) $ replicate k 3
            paheSIMDAdd pkDGK b xorsum3

    xorsumFull3 <- paheSIMDMulScal pkDGK (xorsums !! 0) $ replicate k 3
    cLast <- paheSIMDAdd pkDGK deltaEnc xorsumFull3

   -- log "CIs: "
   -- print =<< mapM (paheDec skDGK) (cLast : ci)
    log "CIs were computed"

    ciShuffled <- shuffle =<< mapM (paheMultBlind pkDGK) (cLast : ci)

    --log "CIs shuffled/blinded: "
    --print =<< mapM (paheDec skDGK) ciShuffled

    sendMulti sock =<< (NE.fromList <$> mapM (paheToBS pkDGK) ciShuffled)
    log "Client: send,waiting"
    zs <- paheFromBS pkGM =<< receive sock
    log "Client: computing eps"

    let compeps = do
          let sMask = map (bool 1 0 . (== 1)) s0
          let sMaskNeg = map (\x -> 1 - x) sMask
          -- zs * s + (1-zs) * neg s
          a <- paheSIMDMulScal pkGM zs sMask
          oneMinZs <- paheSIMDSub pkGM (paheOne pkGM) zs
          c <- paheSIMDMulScal pkGM oneMinZs sMaskNeg
          paheSIMDAdd pkGM a c

    eps <- compeps

    log "Client: dgk ended"
    pure eps

dgkServer ::
       (Pahe sDGK, Pahe sGM)
    => Socket Rep
    -> PaheSk sDGK
    -> PaheSk sGM
    -> Int
    -> [Integer]
    -> IO ()
dgkServer sock skDGK skGM l cs = do
    log "Server: dgk started"
    let pkDGK = paheToPublic skDGK
    let pkGM = paheToPublic skGM
    let k = paheK pkDGK

    let cbits = map (\i -> map (\c -> bool 0 1 $ testBit c i) cs) [0..l-1]
    --log $ "Server cbits: " <> show cbits

    _ <- receive sock

    sendMulti sock =<< (NE.fromList <$> mapM (paheToBS pkDGK <=< paheEnc pkDGK) cbits)

    es <- mapM (paheFromBS pkDGK) =<< receiveMulti sock
    esDecr <- mapM (paheDec skDGK) es
    log $ "Server decrypted:" <> show esDecr
    let zeroes = map (bool 1 0 . (== 0)) $
                 foldr (\e acc -> map (uncurry (*)) $ zip e acc)
                       (replicate k 1) esDecr

    log $ "Server zeroes: " <> show zeroes

    enczeroes <- paheEnc pkGM zeroes
    send sock [] =<< paheToBS pkGM enczeroes

    log "Server: dgk exited"


----------------------------------------------------------------------------
-- Secure Comparison
----------------------------------------------------------------------------

-- | Compute y <= x jointly with secret inputs. Client has r, server has c.
secureCompareClient ::
       (Pahe sTop, Pahe sDGK, Pahe sGM)
    => Socket Req
    -> PahePk sTop
    -> PahePk sDGK
    -> PahePk sGM
    -> Int
    -> PaheCiph sTop
    -> PaheCiph sTop
    -> IO (PaheCiph sGM)
secureCompareClient sock pkTop pkDGK pkGM l x y = do
    log "Client: secureCompare started"
    let k = paheK pkDGK

    rhos::[Integer] <- replicateM k $ randomRIO (0, 2^(l + lambda) - 1)
    s1 <- paheSIMDAdd pkTop x =<< paheEnc pkTop (map (+(2^l)) rhos)
    gamma <- paheSIMDSub pkTop s1 y

    send sock [] =<< paheToBS pkTop gamma

    cDiv2l <- paheFromBS pkGM =<< receive sock

    eps <-
        measureTimeSingle "SC DGK took: " $
        dgkClient sock pkDGK pkGM l $ map (`mod` (2^l)) rhos
    epsNeg <- paheNeg pkGM eps

    rDiv2l <- paheEnc pkGM $ map (`div` (2^l)) rhos
    rPlusEpsNeg <- paheSIMDAdd pkGM rDiv2l epsNeg
    delta <- paheSIMDSub pkGM cDiv2l rPlusEpsNeg

    log "Client: secureCompare exited"
    pure delta

secureCompareServer ::
       (Pahe sTop, Pahe sDGK, Pahe sGM)
    => Socket Rep
    -> PaheSk sTop
    -> PaheSk sDGK
    -> PaheSk sGM
    -> Int
    -> IO ()
secureCompareServer sock skTop skDGK skGM l = do
    let pkTop = paheToPublic skTop
    let pkGM = paheToPublic skGM
    log "Server: securecompare started"

    gamma <- (paheDec skTop <=< paheFromBS pkTop) =<< receive sock
    let cMod2 = map (`mod` (2^l)) gamma
    let cDiv2 = map (`div` (2^l)) gamma
    send sock [] =<< (paheToBS pkGM =<< paheEnc pkGM cDiv2)


    dgkServer sock skDGK skGM l cMod2
    log "Server: securecompare exited"

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
    -> [PaheCiph sTop]
    -> IO (PaheCiph sTop, [Word64])
argmaxClient sock pkTop pkDGK pkGM l vals = do
    let k = paheK pkTop
    let m = length vals
    perm <- shuffle [0..m-1]
    log $ "Perm: " <> show perm

    let loop curMax i = if i == m then pure curMax else do
            log $ "Client loop index " <> show i
            bi <-
                measureTimeSingle "Client argmax SC" $
                secureCompareClient sock pkTop pkDGK pkGM l
                (vals !! (perm !! i)) curMax
            ri <- replicateM k $ randomRIO (0, 2^(l + lambda) - 1)
            si <- replicateM k $ randomRIO (0, 2^(l + lambda) - 1)
            mMasked <- paheSIMDAdd pkTop curMax =<< paheEnc pkTop ri
            aMasked <- paheSIMDAdd pkTop (vals !! (perm !! i)) =<< paheEnc pkTop si

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

    maxval <- loop (vals !!(perm !! 0)) 1
    log "Client: argmax loop ended"

    send sock [] ""
    indices <- map w64FromBs <$> receiveMulti sock

    let indices' = map (fromIntegral . (perm !!) . fromIntegral) indices

    pure (maxval, indices')

argmaxServer ::
       (Pahe sTop, Pahe sDGK, Pahe sGM)
    => Socket Rep
    -> PaheSk sTop
    -> PaheSk sDGK
    -> PaheSk sGM
    -> Int
    -> Int
    -> IO ()
argmaxServer sock skTop skDGK skGM l m = do
    let pkTop = paheToPublic skTop
    let pkGM = paheToPublic skGM
    let k = paheK pkTop

    let loop ixs i = if i == m then pure ixs else do
            log $ "Server loop ixs " <> show i
            secureCompareServer sock skTop skDGK skGM l
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

----------------------------------------------------------------------------
-- Log argmax
----------------------------------------------------------------------------

foldCiphClient ::
       Pahe sTop
    => Socket Req
    -> PahePk sTop
    -> Int
    -> Int -- m such that list has 2^m values
    -> PaheCiph sTop
    -> IO (PaheCiph sTop, PaheCiph sTop)
foldCiphClient sock pk l m values = do
    log "Client: fold start"
    when (2^m > paheK pk) $ error $ "fold client: m is too big: " <> show (m,paheK pk)
    when (m == 0) $ error "foldCiphClient can't fold list of 1"

    let k = paheK pk

    mask1 <- replicateM (2^(m-1)) $ randomRIO (0,2 ^ (l + lambda) - 1)
    mask2 <- replicateM (2^(m-1)) $ randomRIO (0,2 ^ (l + lambda) - 1)
    let mask3::[Integer] = mask1 <> mask2
    mask3Enc <- paheEnc pk $ mask3 <> replicate (paheK pk - (2^m)) 0
    valuesMasked <- paheSIMDAdd pk values mask3Enc

    log "Client: masked, sent"
    send sock [] =<< paheToBS pk valuesMasked

    mask1Enc <- paheEnc pk $ map negate mask1 <> replicate (k - 2^(m-1)) 0
    mask2Enc <- paheEnc pk $ map negate mask2 <> replicate (k - 2^(m-1)) 0

    [rho1Enc,rho2Enc] <- mapM (paheFromBS pk) =<< receiveMulti sock
    log "Client: received, unmasking"

    values1 <- paheSIMDAdd pk rho1Enc mask1Enc
    values2 <- paheSIMDAdd pk rho2Enc mask2Enc

    log "Client: fold end"
    pure (values1,values2)

foldCiphServer ::
       Pahe sTop
    => Socket Rep
    -> PaheSk sTop
    -> Int -- m such that list has 2^m values
    -> IO ()
foldCiphServer sock sk m = do
    let pk = paheToPublic sk
    let k = paheK pk

    rho <- (paheDec sk <=< paheFromBS pk) =<< receive sock
    log "Server: received, splitting"
    let (rho1,rho2) = splitAt (2^(m-1)) $ take (2^m) $ rho

    rho1Enc <- paheEnc pk $ rho1 <> replicate (k - 2^(m-1)) 0
    rho2Enc <- paheEnc pk $ rho2 <> replicate (k - 2^(m-1)) 0

    log "Server: sent back"
    sendMulti sock =<< (NE.fromList <$> mapM (paheToBS pk) [rho1Enc,rho2Enc])

-- Permutes the given ciphertext with a given permutation, returns the perumted list
permuteClient ::
       Pahe sTop
    => Socket Req
    -> PahePk sTop
    -> Int
    -> [Int]
    -> PaheCiph sTop
    -> IO (PaheCiph sTop)
permuteClient sock pk l perm values = do
    let k = paheK pk
    let perminv j = fromMaybe (error "permuteClient perminv") $ findIndex (==j) perm

    maskRaw :: [Integer] <- replicateM k $ randomRIO (0, 2 ^ l - 1)
    maskEnc <- paheEnc pk maskRaw
    valuesMasked <- paheSIMDAdd pk values maskEnc
    send sock [] =<< paheToBS pk valuesMasked

    -- k ciphertexts containing valuesMasked_i in all slots
    replElems <- mapM (paheFromBS pk) =<< receiveMulti sock

    -- combine these k values into one ciphertext
    -- loop i fills [i..k-1] values of the permuted result
    let loop j = if j == k then pure (paheZero pk) else do
            next <- loop (j+1)
            let i = perminv j
            -- We select jth element from (perm^-1 j)
            let selMask = replicate j 0 ++ [1] ++ replicate (k - j - 1) 0
            cur <- paheSIMDMulScal pk (replElems !! i) selMask
            paheSIMDAdd pk cur next


    let permutedMaskNeg = map (\i -> negate (maskRaw !! (perminv i))) [0..k-1]

    permuted <- loop 0

    paheSIMDAdd pk permuted =<< paheEnc pk permutedMaskNeg

permuteServer ::
       Pahe sTop
    => Socket Rep
    -> PaheSk sTop
    -> IO ()
permuteServer sock sk = do
    let pk = paheToPublic sk
    prev <- (paheDec sk <=< paheFromBS pk) =<< receive sock
    let dups = map (\e -> replicate (paheK pk) e) prev
    encDups <- mapM (paheEnc pk) dups
    sendMulti sock =<< (NE.fromList <$> mapM (paheToBS pk) encDups)


argmaxLogClient ::
       (Pahe sTop, Pahe sDGK, Pahe sGM)
    => Socket Req
    -> PahePk sTop
    -> PahePk sDGK
    -> PahePk sGM
    -> Int
    -> Int
    -> PaheCiph sTop
    -> IO (Int, PaheCiph sTop)
argmaxLogClient sock pkTop pkDGK pkGM l m vals = do
    let k = paheK pkTop
    when (2^m > k) $ error "argmaxLogClient m is too big"

    perm <- shuffle [0..k-1]
    log $ "Client: perm " <> show perm
    let perminv j = fromMaybe (error "argmaxLogCli perminv") $ findIndex (==j) perm
    valsPerm <- measureTimeSingle "perm" $ permuteClient sock pkTop l perm vals
    log "Client: perm done"

    let loop acc i = if i == 0 then pure acc else do
            (p1,p2) <- foldCiphClient sock pkTop l i acc
            -- delta is p2 <= p1
            delta <- secureCompareClient sock pkTop pkDGK pkGM l p1 p2
            -- we only care about first 2^(i-1) bits of this mask though
            p1mask <- replicateM k $ randomRIO (0, 2 ^ l - 1)
            p2mask <- replicateM k $ randomRIO (0, 2 ^ l - 1)
            p1masked <- paheSIMDAdd pkTop p1 =<< paheEnc pkTop p1mask
            p2masked <- paheSIMDAdd pkTop p2 =<< paheEnc pkTop p2mask

            pXMaskedBS <- mapM (paheToBS pkTop) [p1masked,p2masked]
            deltaBS <- paheToBS pkGM delta
            sendMulti sock $ NE.fromList (deltaBS:pXMaskedBS)

            [deltaTop,combinedMasked] <-
                mapM (paheFromBS pkTop) =<< receiveMulti sock
            deltaTopNeg <- paheSIMDSub pkTop (paheOne pkTop) deltaTop

            -- unmask by doing combinedMasked - delta*p1 - deltaNeg*p2
            combined <- do
                tmp1 <- paheSIMDMulScal pkTop deltaTop (map negate p1mask)
                tmp2 <- paheSIMDMulScal pkTop deltaTopNeg (map negate p2mask)
                paheSIMDAdd pkTop combinedMasked =<< paheSIMDAdd pkTop tmp1 tmp2

            loop combined (i-1)

    maxEl <- loop valsPerm m

    send sock [] ""
    maxIndex <- fromIntegral . w64FromBs <$> receive sock

    pure (perminv maxIndex, maxEl)

argmaxLogServer ::
       (Pahe sTop, Pahe sDGK, Pahe sGM)
    => Socket Rep
    -> PaheSk sTop
    -> PaheSk sDGK
    -> PaheSk sGM
    -> Int
    -> Int
    -> IO ()
argmaxLogServer sock skTop skDGK skGM l m = do
    let pkTop = paheToPublic skTop
    let pkGM = paheToPublic skGM

    permuteServer sock skTop

    let loop (ixs::[Integer]) i = if i == 0 then pure ixs else do
            log $ "Server, ixs: " <> show ixs
            foldCiphServer sock skTop i
            secureCompareServer sock skTop skDGK skGM l

            [deltaBS,p1bs,p2bs] <- receiveMulti sock
            delta <- paheDec skGM =<< paheFromBS pkGM deltaBS
            [p1,p2] <-
                mapM (paheDec skTop <=< paheFromBS pkTop) [p1bs,p2bs]
            let pCombined = simdadd (simdmul p1 delta)
                                    (simdmul p2 (map (\x -> 1 - x) delta))
            sendMulti sock =<<
                NE.fromList <$>
                mapM (paheToBS pkTop <=< paheEnc pkTop) [delta,pCombined]
            let ixs' =
                    let delta' = take (2^(i-1)) delta in
                    let (ixs0, ixs1) = splitAt (2^(i-1)) ixs in
                    simdadd (simdmul ixs0 delta')
                            (simdmul ixs1 (map (\x -> 1 - x) delta'))
            loop ixs' (i-1)

    ixs <- loop [0..(2^m - 1)] m
    log $ "Server, ixs: " <> show ixs
    let maxIx = ixs !! 0
    log $ "Server: argmax loop ended, indices: " <> show maxIx

    _ <- receive sock
    send sock [] $ w64ToBs $ fromIntegral maxIx

    log "Server: exiting"


----------------------------------------------------------------------------
-- Argmax Log 2
----------------------------------------------------------------------------

-- Permutes list of 2k elements (passed as 2 ciphertexts) into 2
-- another ciphertexts.
permuteFoldClient ::
       Pahe sTop
    => Socket Req
    -> PahePk sTop
    -> Int
    -> [Int]
    -> PaheCiph sTop
    -> PaheCiph sTop
    -> IO (PaheCiph sTop, PaheCiph sTop)
permuteFoldClient sock pk l perm v1 v2 = do
    let k = paheK pk
    let k2 = k `div` 2
    when (k2 * 2 /= k) $ error "permuteFoldClient doesn't support non-even k"

    let perminv = map (\j ->fromMaybe (error "permuteClient perminv") $
                        findIndex (==j) perm) [0..2*k-1]

    mask1Raw <- replicateM k $ randomRIO (0, 2 ^ l - 1)
    mask2Raw <- replicateM k $ randomRIO (0, 2 ^ l - 1)
    mask1Enc <- paheEnc pk mask1Raw
    mask2Enc <- paheEnc pk mask2Raw
    v1Masked <- paheSIMDAdd pk v1 mask1Enc
    v2Masked <- paheSIMDAdd pk v2 mask2Enc

    sendMulti sock =<< NE.fromList <$> mapM (paheToBS pk) [v1Masked,v2Masked]

    -- k ciphertexts containing valuesMasked_i in all slots
    replElems <- mapM (paheFromBS pk) =<< receiveMulti sock

    let loop w j = if j == k then pure (paheZero pk) else do
            next <- loop w (j+1)
            let i = perminv !! (w+j)
            -- We select jth element from (perm^-1 j)
            let selMask = replicate j 0 ++ [1] ++ replicate (k - j - 1) 0
            cur <- paheSIMDMulScal pk (replElems !! i) selMask
            paheSIMDAdd pk cur next

    permuted1 <- loop 0 0
    permuted2 <- loop k 0

    let permutedMaskNeg = map (\i -> negate ((mask1Raw++mask2Raw) !! (perminv !! i))) [0..2*k-1]
    let m1 = take k permutedMaskNeg
    let m2 = drop k permutedMaskNeg

    r1 <- paheSIMDAdd pk permuted1 =<< paheEnc pk m1
    r2 <- paheSIMDAdd pk permuted2 =<< paheEnc pk m2

    pure (r1,r2)

permuteFoldServer ::
       Pahe sTop
    => Socket Rep
    -> PaheSk sTop
    -> IO ()
permuteFoldServer sock sk = do
    let pk = paheToPublic sk
    [p1,p2] <- mapM (paheDec sk <=< paheFromBS pk) =<< receiveMulti sock
    let dups = map (\e -> replicate (paheK pk) e) $ p1 ++ p2
    encDups <- mapM (paheEnc pk) dups
    sendMulti sock =<< (NE.fromList <$> mapM (paheToBS pk) encDups)


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
    (v1Perm,v2Perm) <- measureTimeSingle "perm" $ permuteFoldClient sock pkTop l perm v1 v2
    log "Client: perm done"

    -- p1 and p2 are of length 2^i each
    let loop p1 p2 i = do
            log $ "Client loop index " <> show i
            let curLen = 2^i
            -- delta is p2 <= p1
            delta <- secureCompareClient sock pkTop pkDGK pkGM l p1 p2
            -- we only care about first 2^(i-1) bits of this mask though
            p1mask <- replicateM curLen $ randomRIO (0, 2 ^ l - 1)
            p2mask <- replicateM curLen $ randomRIO (0, 2 ^ l - 1)
            p1masked <- paheSIMDAdd pkTop p1 =<< paheEnc pkTop (p1mask ++ replicate (k-curLen) 0)
            p2masked <- paheSIMDAdd pkTop p2 =<< paheEnc pkTop (p2mask ++ replicate (k-curLen) 0)

            pXMaskedBS <- mapM (paheToBS pkTop) [p1masked,p2masked]
            deltaBS <- paheToBS pkGM delta
            sendMulti sock $ NE.fromList (deltaBS:pXMaskedBS)

            let p1maskNeg = map negate p1mask
            let p2maskNeg = map negate p2mask

            when (i > 0) $ do
                -- each of these is of size 2^(i-1)
                [delta1,delta2,combM1,combM2] <-
                    mapM (paheFromBS pkTop) =<< receiveMulti sock
                delta1Neg <- paheSIMDSub pkTop (paheOne pkTop) delta1
                delta2Neg <- paheSIMDSub pkTop (paheOne pkTop) delta2

                let nextLen = curLen`div`2
                let getlow xs = take nextLen xs ++ replicate (k-nextLen) 0
                let gethigh xs = take nextLen (drop nextLen xs) ++ replicate (k-nextLen) 0

                -- unmask by doing combinedMasked - delta*p1 - deltaNeg*p2
                comb1 <- do
                    tmp1 <- paheSIMDMulScal pkTop delta1 $ getlow p1maskNeg
                    tmp2 <- paheSIMDMulScal pkTop delta1Neg $ getlow p2maskNeg
                    paheSIMDAdd pkTop combM1 =<< paheSIMDAdd pkTop tmp1 tmp2

                comb2 <- do
                    tmp1 <- paheSIMDMulScal pkTop delta2 $ gethigh p1maskNeg
                    tmp2 <- paheSIMDMulScal pkTop delta2Neg $ gethigh p2maskNeg
                    paheSIMDAdd pkTop combM2 =<< paheSIMDAdd pkTop tmp1 tmp2

                loop comb1 comb2 (i-1)

    loop v1Perm v2Perm m

    maxIndex <- fromIntegral . w64FromBs <$> receive sock

    pure $ perminv maxIndex

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
    let k = paheK pkTop

    permuteFoldServer sock skTop

    -- at step i we're comparing two arrays of size 2^i each
    -- so the first step has index m-1
    let loop (ixs::[Integer]) i = do
            log $ "Server loop index " <> show i
            secureCompareServer sock skTop skDGK skGM l

            let curLen = 2^i

            [deltaBS,p1bs,p2bs] <- receiveMulti sock
            delta <- paheDec skGM =<< paheFromBS pkGM deltaBS
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
                let getlow xs = take nextLen xs ++ replicate (k-nextLen) 0
                let gethigh xs = take nextLen (drop nextLen xs) ++ replicate (k-nextLen) 0

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

runProtocol :: IO ()
runProtocol =
    withContext $ \ctx ->
    withSocket ctx Req $ \req ->
    withSocket ctx Rep $ \rep -> do
      putTextLn "Initialised the context, generating params"
      bind rep "inproc://argmax"
      connect req "inproc://argmax"

      putTextLn "Keygen..."
      -- SIMD parameter
      let k = 16
      -- bit size of numbers we compare
      let l = 64
      -- Number of argmax input elements
      let m::Int = 2 ^ (log2 (fromIntegral k) - 1 :: Integer)
      let mlog::Int = log2 (m-1)
      -- plaintext space size
      --let margin = 2^(lambda + l)
      let margin = 2^(l+3)

      putTextLn $ "mlog,m: " <> show (mlog,m)

      -- system used to carry long secureCompare results
      skTop <- paheKeyGen @PailSep k (2^(lambda + l + 100))
      --let skTop = skDGK
      let pkTop = paheToPublic skTop

      -- system used for DGK comparison
      --skDGK <- paheKeyGen @PailSep k (2^(lambda+l))
      skDGK <- paheKeyGen @DgkCrt k (3 + 3 * fromIntegral l)
      let pkDGK = paheToPublic skDGK

      -- system used to carry QR results
      skGM <- paheKeyGen @GMSep k margin
      --let skGM = skDGK
      let pkGM = paheToPublic skGM


      let testLog2Argmax = do
            v1 <- replicateM k $ randomRIO (0,2^l-1)
            v2 <- replicateM k $ randomRIO (0,2^l-1)
            let vals = v1 ++ v2
            putTextLn $ "Values for argmax: " <> show vals
            let expectedMax = foldr1 max vals
            e1 <- paheEnc pkTop v1
            e2 <- paheEnc pkTop v2

            (ix,()) <-
                measureTimeSingle "log Argmax" $
                concurrently
                (argmaxLog2Client req pkTop pkDGK pkGM l mlog e1 e2)
                (argmaxLog2Server rep skTop skDGK skGM l mlog)

            unless (vals !! ix == expectedMax) $ do
                putTextLn $ "vals: " <> show vals
                error $ "logArgmax broken, ix: " <> show ix

      let testPermFold = do
            perm <- shuffle [0..2*k-1]
            putTextLn $ "perm " <> show perm

            f1 <- replicateM k $ randomRIO (0,2^l-1)
            f2 <- replicateM k $ randomRIO (0,2^l-1)
            putTextLn $ "Elements to shufle: " <> show (f1,f2)
            f1Enc <- paheEnc pkTop f1
            f2Enc <- paheEnc pkTop f2

            ((v1,v2),()) <-
                concurrently
                (permuteFoldClient req pkTop l perm f1Enc f2Enc)
                (permuteFoldServer rep skTop)

            print =<< paheDec skTop v1
            print =<< paheDec skTop v2

      let testLogArgmax = do
            vals <- replicateM m $ randomRIO (0,2^l-1)
            let expectedMax = foldr1 max vals
            let expectedMaxIx =
                    fromMaybe (error "") $ findIndex (==expectedMax) vals
            encVals <- paheEnc pkTop $ vals <> replicate (k - m) 0

            ((ix,el),()) <-
                measureTimeSingle "log Argmax" $
                concurrently
                (argmaxLogClient req pkTop pkDGK pkGM l mlog encVals)
                (argmaxLogServer rep skTop skDGK skGM l mlog)

            decEl <- paheDec skTop el
            unless (ix == fromIntegral expectedMaxIx) $ do
                putTextLn $ "vals: " <> show vals
                error $ "logArgmax broken, ix: " <> show (ix,expectedMaxIx)
            unless (decEl !! 0 == expectedMax) $ do
                putTextLn $ "vals: " <> show vals
                error $ "logArgmax broken, el: " <> show (decEl !! 0, expectedMax)

      let testPerm = do
            perm <- shuffle [0..k-1]
            putTextLn $ "perm " <> show perm

            f <- replicateM k $ randomRIO (0,2^l-1)
            print f
            fEnc <- paheEnc pkTop f

            (valsPerm,()) <-
                concurrently
                (permuteClient req pkTop l perm fEnc)
                (permuteServer rep skTop)

            valsDec <- paheDec skTop valsPerm
            print valsDec

      let testFold = do
              f <- replicateM (2^m) $ randomRIO (0,2^l-1)
              putTextLn $ "m: " <> show m
              putTextLn $ "f: " <> show f
              fEnc <- paheEnc pkTop $ f <> replicate (k-2^m) 5

              ((f1,f2),()) <-
                  measureTimeSingle "fold" $
                  concurrently
                  (foldCiphClient req pkTop l m fEnc)
                  (foldCiphServer rep skTop m)

              print f
              print =<< paheDec skTop f1
              print =<< paheDec skTop f2

      let testArgmax = do
              vals <- replicateM m $ replicateM k $ randomRIO (0,2^l-1)
              print vals
              let expected = foldr1 (\l1 l2 -> map (uncurry max) $ zip l1 l2) vals
              encVals <- mapM (paheEnc pkTop) vals


              ((maxes,indices),()) <-
                  measureTimeSingle "Argmax" $
                  concurrently
                  (argmaxClient req pkTop pkDGK pkGM l encVals)
                  (argmaxServer rep skTop skDGK skGM l m)

              putTextLn "Maxes/indices"
              decMaxes <- paheDec skTop maxes
              print decMaxes
              print indices

              if (decMaxes /= expected)
                  then error "Argmax failed" else putTextLn "OK"


      let testCompare = replicateM_ 100 $ do
              xs <- replicateM k $ randomRIO (0,2^l-1)
              ys <- replicateM k $ randomRIO (0,2^l-1)
              let expected = map (\(x,y) -> x >= y) $ zip xs ys

              xsEnc <- paheEnc pkTop xs
              ysEnc <- paheEnc pkTop ys

              (gamma,()) <-
                  measureTimeSingle "SecureCompare" $
                  concurrently
                  (secureCompareClient req pkTop pkDGK pkGM l xsEnc ysEnc)
                  (secureCompareServer rep skTop skDGK skGM l)

              secCompRes <- paheDec skGM gamma
              unless (map (==1) secCompRes == expected) $ do
                  print xs
                  print ys
                  putTextLn $ "Expected: " <> show expected
                  putTextLn $ "Got:      " <> show secCompRes
                  putTextLn $ "          " <> show (map (==1) secCompRes)
                  error "Mismatch"

      let testDGK = replicateM_ 100 $ do
              cs <- replicateM k $ randomRIO (0,2^l-1)
              rs <- replicateM k $ randomRIO (0,2^l-1)
              let expected = map (\(c,r) -> r <= c) $ zip cs rs

              putTextLn "Starting the protocol"
              (eps,()) <-
                  measureTimeSingle "DGKcomp" $
                  concurrently
                  (dgkClient req pkDGK pkGM l rs)
                  (dgkServer rep skDGK skGM l cs)

              dgkRes <- map (== 1) <$> paheDec skGM eps
              unless (dgkRes == expected) $ do
                  print cs
                  print rs
                  putTextLn $ "Expected: " <> show expected
                  putTextLn $ "Got:      " <> show dgkRes
                  error "Mismatch"

      testLog2Argmax
      --testPermFold
      --testLogArgmax
      --testArgmax
      --testPerm
      --testFold
      --testArgmax
      --testDGK
      --testCompare
