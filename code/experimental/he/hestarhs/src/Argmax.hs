-- | Implementation of argmax protocol

module Argmax where

import Universum

import Control.Concurrent (threadDelay, withMVar)
import Control.Concurrent.Async (concurrently)
import Data.Array.IO
import Data.Bits (testBit)
import qualified Data.ByteString as BS
import Data.List (findIndex, (!!))
import qualified Data.List.NonEmpty as NE
import qualified Data.Set as S
import Data.Time.Clock.POSIX (getPOSIXTime)
import qualified Data.Time.Clock.POSIX as P
import qualified Foreign.Marshal as A
import System.IO.Unsafe (unsafePerformIO)
import System.Random (randomIO, randomRIO)
import System.ZMQ4

import Hacl
import qualified Lib as L
import Playground
import TestHacl

getCurrentTimeMs :: IO Integer
getCurrentTimeMs = floor . (*1000) <$> getPOSIXTime

lMVar :: MVar ()
lMVar = unsafePerformIO $ newMVar ()

log :: MonadIO m => Text -> m ()
log x = do
    t <- liftIO getCurrentTimeMs
    liftIO $ withMVar lMVar $ \() ->
      putTextLn (show (t`div`1000) <> "." <> show (t`mod`1000) <> " " <> x) >> pure ()

lambda :: Integral a => a
lambda = 80

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


data EncContext s =
    EncContext
        { encZero   :: PaheCiph s
        , encOne    :: PaheCiph s
        , encMinOne :: PaheCiph s
        }

newEncContext :: Pahe s => PahePk s -> IO (EncContext s)
newEncContext pk = do
    let k = paheK pk
    encZero <- paheEnc pk $ replicate k 0
    encOne <- paheEnc pk $ replicate k 1
    encMinOne <- paheEnc pk $ replicate k (-1)
    pure EncContext{..}

-- | Compute r <= c jointly. Client has r, server has c.
dgkClient :: Pahe s => Socket Req -> PahePk s -> EncContext s -> Int -> [Integer] -> IO (PaheCiph s)
dgkClient sock pk EncContext{..} l rs = do

    let k = paheK pk
    log "Client: dgk started"
    send sock [] "init"

    let rbits = map (\i -> map (\c -> bool 0 1 $ testBit c i) rs) [0..l-1]
   -- log $ "Client rbits: " <> show rbits
    encRBits <- mapM (paheEnc pk) rbits

    cs <- mapM (paheFromBS pk) =<< receiveMulti sock


    log "Client: computing xors"
    xors <- forM (cs `zip` [0..]) $ \(ci,i) -> do
        let bitmask = rbits !! i
        let bitmaskNeg = map (\x -> 1 - x) bitmask

        -- ci * maskNeg + (1-ci) * mask
        a <- paheSIMDMulScal pk ci bitmaskNeg
        oneMinCi <- paheSIMDSub pk encOne ci
        c <- paheSIMDMulScal pk oneMinCi bitmask
        paheSIMDAdd pk a c

    delta <- replicateM k (randomRIO (0,1))
    deltaEnc <- paheEnc pk delta
    let s0 = map (\i -> 1 - 2 * i) delta
    --log $ "Client: s = " <> show s0
    s <- paheEnc pk s0

    let computeXorSums i prev = do
            nextXorSum <- paheSIMDAdd pk prev (xors !! i)
            xorsTail <- if i == 0 then pure [] else computeXorSums (i-1) nextXorSum
            pure $ nextXorSum : xorsTail
    xorsums <- reverse <$> computeXorSums (l-1) encZero

    log "Client: computing cis"
    ci <- forM [0..l-1] $ \i -> do
        a <- paheSIMDAdd pk s (encRBits !! i)
        b <- paheSIMDSub pk a (cs !! i)

        if i == l-1 then pure b else do
            xorsum3 <- paheSIMDMulScal pk (xorsums !! (i+1)) $ replicate k 3
            paheSIMDAdd pk b xorsum3

    xorsumFull3 <- paheSIMDMulScal pk (xorsums !! 0) $ replicate k 3
    cLast <- paheSIMDAdd pk deltaEnc xorsumFull3

    ciShuffled <- shuffle =<< mapM (paheMultBlind pk) (cLast : ci)

    sendMulti sock =<< (NE.fromList <$> mapM (paheToBS pk) ciShuffled)
    log "Client: send,waiting"
    zs <- paheFromBS pk =<< receive sock

    let compeps = do
          let sMask = map (bool 1 0 . (== 1)) s0
          let sMaskNeg = map (\x -> 1 - x) sMask
          -- zs * s + (1-zs) * neg s
          a <- paheSIMDMulScal pk zs sMask
          oneMinZs <- paheSIMDSub pk encOne zs
          c <- paheSIMDMulScal pk oneMinZs sMaskNeg
          paheSIMDAdd pk a c

    eps <- compeps

    log "Client: dgk ended"
    pure eps

dgkServer :: Pahe s => Socket Rep -> PaheSk s -> Int -> [Integer] -> IO ()
dgkServer sock sk l cs = do
    log "Server: dgk started"
    let pk = paheToPublic sk
    let k = paheK pk

    let cbits = map (\i -> map (\c -> bool 0 1 $ testBit c i) cs) [0..l-1]
--    log $ "Server cbits: " <> show cbits

    _ <- receive sock

    sendMulti sock =<< (NE.fromList <$> mapM (paheToBS pk <=< paheEnc pk) cbits)

    es <- mapM (paheFromBS pk) =<< receiveMulti sock
    esDecr <- mapM (paheDec sk) es
    let zeroes = map (bool 1 0 . (== 0)) $
                 foldr (\e acc -> map (uncurry (*)) $ zip e acc)
                       (replicate k 1) esDecr

    enczeroes <- paheEnc pk zeroes
    send sock [] =<< paheToBS pk enczeroes

    log "Server: dgk exited"


-- | Compute y <= x jointly with secret inputs. Client has r, server has c.
secureCompareClient ::
       Pahe s
    => Socket Req
    -> PahePk s
    -> EncContext s
    -> Int
    -> PaheCiph s
    -> PaheCiph s
    -> IO (PaheCiph s)
secureCompareClient sock pk ctx@EncContext{..} l x y = do
    log "Client: secureCompare started"
    let k = paheK pk

    rhos::[Integer] <- replicateM k $ randomRIO (0, 2^(l + lambda) - 1)
    s0 <- paheEnc pk (map (+(2^l)) rhos)
    s1 <- paheSIMDAdd pk s0 x
    gamma <- paheSIMDSub pk s1 y

    send sock [] =<< paheToBS pk gamma

    cDiv2l <- paheFromBS pk =<< receive sock

    eps <- dgkClient sock pk ctx l $ map (`mod` (2^l)) rhos

    epsNeg <- paheSIMDSub pk encOne eps

    rDiv2 <- paheEnc pk $ map (`div` (2^l)) rhos
    rPlusEpsNeg <- paheSIMDAdd pk rDiv2 epsNeg
    delta <- paheSIMDSub pk cDiv2l rPlusEpsNeg

    log "Client: secureCompare exited"
    pure delta

secureCompareServer :: Pahe s => Socket Rep -> PaheSk s -> Int -> IO ()
secureCompareServer sock sk l = do
    let pk = paheToPublic sk
    log "Server: securecompare started"

    gamma <- (paheDec sk <=< paheFromBS pk) =<< receive sock
    let cMod2 = map (`mod` (2^l)) gamma
    let cDiv2 = map (`div` (2^l)) gamma
    send sock [] =<< (paheToBS pk =<< paheEnc pk cDiv2)

    dgkServer sock sk l cMod2
    log "Server: securecompare exited"

w64ToBs :: Word64 -> ByteString
w64ToBs = BS.pack . map fromIntegral . inbase 256 . fromIntegral

w64FromBs :: ByteString -> Word64
w64FromBs = fromIntegral . frombase 256 . map fromIntegral . BS.unpack

argmaxClient ::
       Pahe s
    => Socket Req
    -> PahePk s
    -> EncContext s
    -> Int
    -> [PaheCiph s]
    -> IO (PaheCiph s, [Word64])
argmaxClient sock pk ctx@EncContext{..} l vals = do
    let k = paheK pk
    let m = length vals
    perm <- shuffle [0..m-1]
    log $ "Perm: " <> show perm

    oneEnc <- paheEnc pk $ replicate k 1
    let loop curMax i = if i == m then pure curMax else do
            log $ "Client loop index " <> show i
            bi <- secureCompareClient sock pk ctx l
                (vals !! (perm !! i)) curMax
            ri <- replicateM k $ randomRIO (0, 2^(l + lambda) - 1)
            si <- replicateM k $ randomRIO (0, 2^(l + lambda) - 1)
            mMasked <- paheSIMDAdd pk curMax =<< paheEnc pk ri
            aMasked <- paheSIMDAdd pk (vals !! (perm !! i)) =<< paheEnc pk si
            sendMulti sock =<<
                (NE.fromList <$> mapM (paheToBS pk) [bi, mMasked, aMasked])

            vi <- paheFromBS pk =<< receive sock
            newMax <- do
                biNeg <- paheSIMDSub pk bi oneEnc
                tmp1 <- paheSIMDMulScal pk biNeg ri
                tmp2 <- paheSIMDMulScal pk bi si
                tmp3 <- paheSIMDAdd pk vi tmp1
                paheSIMDSub pk tmp3 tmp2

            loop newMax (i+1)

    maxval <- loop (vals !!(perm !! 0)) 1
    log "Client: argmax loop ended"

    send sock [] ""
    indices <- map w64FromBs <$> receiveMulti sock

    let indices' = map (fromIntegral . (perm !!) . fromIntegral) indices

    pure (maxval, indices')


argmaxServer :: Pahe s => Socket Rep -> PaheSk s -> Int -> Int -> IO ()
argmaxServer sock sk l m = do
    let pk = paheToPublic sk
    let k = paheK pk

    let loop ixs i = if i == m then pure ixs else do
            log $ "Server loop ixs " <> show i
            secureCompareServer sock sk l
            [bi0,mMasked,aMasked] <-
                mapM (paheFromBS pk) =<< receiveMulti sock
            log $ "Server loop: got values from client"
            bi <- paheDec sk bi0
            let biNeg = map (\x -> 1 - x) bi

            vi <- do
                -- bi * ai + (1-bi) * mi
                tmp1 <- paheSIMDMulScal pk aMasked bi
                tmp2 <- paheSIMDMulScal pk mMasked biNeg
                paheSIMDAdd pk tmp1 tmp2

            send sock [] =<< paheToBS pk vi

            let ixs' =
                    map (\j -> if bi !! j == 1 then i else ixs !! j) [0..k-1]
            log "Server loop end"
            loop ixs' (i+1)

    indices <- loop (replicate k 0) 1
    log $ "Server: argmax loop ended, indices: " <> show indices

    _ <- receive sock
    sendMulti sock $ NE.fromList $ map (w64ToBs . fromIntegral) indices

    log "Server: exiting"

foldCiphClient ::
       Pahe s
    => Socket Req
    -> PahePk s
    -> Int
    -> Int -- m such that list has 2^m values
    -> PaheCiph s
    -> IO (PaheCiph s, PaheCiph s)
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
       Pahe s
    => Socket Rep
    -> PaheSk s
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

-- | Returns a ciphertext filled with the value of zeroth element of
-- the input ciphertext
fill0Client ::
       Pahe s => Socket Req -> PahePk s -> PaheCiph s -> Int -> IO (PaheCiph s)
fill0Client sock pk values l = do
    maskRaw <- replicateM (paheK pk) $ randomRIO (0, 2 ^ l - 1)
    maskEnc <- paheEnc pk maskRaw
    valuesMasked <- paheSIMDAdd pk values maskEnc
    send sock [] =<< paheToBS pk valuesMasked

    maskEncNeg <- paheEnc pk $ map negate maskRaw

    rho <- paheFromBS pk =<< receive sock

    paheSIMDAdd pk rho maskEncNeg

fill0Server :: Pahe s => Socket Rep -> PaheSk s -> IO ()
fill0Server sock sk = do
    let pk = paheToPublic sk
    prev <- (paheDec sk <=< paheFromBS pk) =<< receive sock
    next <- paheEnc pk $ replicate (paheK pk) (prev !! 0)
    send sock [] =<< paheToBS pk next

-- Permutes the given ciphertext with a given permutation, returns the perumt
permuteClient ::
       Pahe s
    => Socket Req
    -> PahePk s
    -> EncContext s
    -> Int
    -> [Int]
    -> PaheCiph s
    -> IO (PaheCiph s)
permuteClient sock pk EncContext{..} l perm values = do
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
    let loop j = if j == k then pure encZero else do
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
       Pahe s
    => Socket Rep
    -> PaheSk s
    -> IO ()
permuteServer sock sk = do
    let pk = paheToPublic sk
    prev <- (paheDec sk <=< paheFromBS pk) =<< receive sock
    let dups = map (\e -> replicate (paheK pk) e) prev
    encDups <- mapM (paheEnc pk) dups
    sendMulti sock =<< (NE.fromList <$> mapM (paheToBS pk) encDups)


argmaxLogClient ::
       Pahe s
    => Socket Req
    -> PahePk s
    -> EncContext s
    -> Int
    -> Int
    -> PaheCiph s
    -> IO (Int, PaheCiph s)
argmaxLogClient sock pk ctx@EncContext{..} l m vals = do
    let k = paheK pk
    when (2^m > k) $ error "argmaxLogClient m is too big"

    perm <- shuffle [0..k-1]
    log $ "Client: perm " <> show perm
    let perminv j = fromMaybe (error "argmaxLogCli perminv") $ findIndex (==j) perm
    valsPerm <- permuteClient sock pk ctx l perm vals
    log "Client: perm done"

    let loop acc i = if i == 0 then pure acc else do
            (p1,p2) <- foldCiphClient sock pk l i acc
            -- delta is p2 <= p1
            delta <- secureCompareClient sock pk ctx l p1 p2
            -- we only care about first 2^(i-1) bits of this mask though
            p1mask <- replicateM k $ randomRIO (0, 2 ^ l - 1)
            p2mask <- replicateM k $ randomRIO (0, 2 ^ l - 1)
            p1masked <- paheSIMDAdd pk p1 =<< paheEnc pk p1mask
            p2masked <- paheSIMDAdd pk p2 =<< paheEnc pk p2mask
            sendMulti sock =<< NE.fromList <$> mapM (paheToBS pk) [delta,p1masked,p2masked]

            deltaNeg <- paheSIMDSub pk encOne delta

            combinedMasked <- paheFromBS pk =<< receive sock
            -- unmask by doing combinedMasked - delta*p1 - deltaNeg*p2
            combined <- do
                tmp1 <- paheSIMDMulScal pk delta (map negate p1mask)
                tmp2 <- paheSIMDMulScal pk deltaNeg (map negate p2mask)
                paheSIMDAdd pk combinedMasked =<< paheSIMDAdd pk tmp1 tmp2

            loop combined (i-1)

    maxEl <- loop valsPerm m

    send sock [] ""
    maxIndex <- fromIntegral . w64FromBs <$> receive sock

    pure (perminv maxIndex, maxEl)

argmaxLogServer :: Pahe s => Socket Rep -> PaheSk s -> Int -> Int -> IO ()
argmaxLogServer sock sk l m = do
    let pk = paheToPublic sk

    permuteServer sock sk

    let loop (ixs::[Integer]) i = if i == 0 then pure ixs else do
            log $ "Server, ixs: " <> show ixs
            log "Server starting fold"
            foldCiphServer sock sk i
            log "Server starting secure compare"
            secureCompareServer sock sk l
            [delta,p1,p2] <-
                mapM (paheDec sk <=< paheFromBS pk) =<< receiveMulti sock
            let pCombined = simdadd (simdmul p1 delta)
                                    (simdmul p2 (map (\x -> 1 - x) delta))
            send sock [] =<< paheToBS pk =<< paheEnc pk pCombined
            -- TODO update indices
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


runProtocol :: IO ()
runProtocol =
    withContext $ \ctx ->
    withSocket ctx Req $ \req ->
    withSocket ctx Rep $ \rep -> do
      putTextLn "Initialised the context, generating params"
      bind rep "inproc://argmax"
      connect req "inproc://argmax"

      putTextLn "Keygen..."
      let k = 16
      sk <- paheKeyGen @PailSep k
      let pk = paheToPublic sk
      eCtx <- newEncContext pk
      let l = 7

      let testLogArgmax = do
              let m = fromIntegral $ log2 (fromIntegral k) - 1
              vals <- replicateM (2^m) $ randomRIO (0,2^l-1)
              putTextLn $ "m: " <> show m
              putTextLn $ "vals: " <> show vals
              print vals
              let expectedMax = foldr1 max vals
              let expectedMaxIx =
                      fromMaybe (error "") $ findIndex (==expectedMax) vals
              encVals <- paheEnc pk $ vals <> replicate (k - 2^m) 0

              ((ix,el),()) <-
                  measureTimeSingle "log Argmax" $
                  concurrently
                  (argmaxLogClient req pk eCtx l m encVals)
                  (argmaxLogServer rep sk l m)

              unless (ix == fromIntegral expectedMaxIx) $
                  error $ "logArgmax broken, ix: " <> show (ix,expectedMaxIx)
              decEl <- paheDec sk el
              unless (decEl !! 0 == expectedMax) $
                  error $ "logArgmax broken, el: " <> show (decEl !! 0, expectedMax)

      let testPerm = do
            perm <- shuffle [0..k-1]
            putTextLn $ "perm " <> show perm

            f <- replicateM k $ randomRIO (0,2^l-1)
            print f
            fEnc <- paheEnc pk f

            (valsPerm,()) <-
                concurrently
                (permuteClient req pk eCtx l perm fEnc)
                (permuteServer rep sk)

            valsDec <- paheDec sk valsPerm
            print valsDec

      let testFold = do
              let m = (fromIntegral $ log2 (fromIntegral k) - 1) - 1
              f <- replicateM (2^m) $ randomRIO (0,2^l-1)
              putTextLn $ "m: " <> show m
              putTextLn $ "f: " <> show f
              fEnc <- paheEnc pk $ f <> replicate (k-2^m) 5

              ((f1,f2),()) <-
                  measureTimeSingle "fold" $
                  concurrently
                  (foldCiphClient req pk l m fEnc)
                  (foldCiphServer rep sk m)

              print f
              print =<< paheDec sk f1
              print =<< paheDec sk f2

      let testArgmax = replicateM_ 1 $ do
              let m = 6
              vals <- replicateM m $ replicateM k $ randomRIO (0,2^l-1)
              print vals
              let expected = foldr1 (\l1 l2 -> map (uncurry max) $ zip l1 l2) vals
              encVals <- mapM (paheEnc pk) vals


              ((maxes,indices),()) <-
                  measureTimeSingle "Argmax" $
                  concurrently
                  (argmaxClient req pk eCtx l encVals)
                  (argmaxServer rep sk l m)

              putTextLn "Maxes/indices"
              decMaxes <- paheDec sk maxes
              print decMaxes
              print indices

              if (decMaxes /= expected)
                  then error "Argmax failed" else putTextLn "OK"


      let testCompare = replicateM_ 10 $ do
              cs <- replicateM k $ randomRIO (0,2^l-1)
              rs <- replicateM k $ randomRIO (0,2^l-1)
              print cs
              print rs
              let expected = map (\(c,r) -> r <= c) $ zip cs rs

              csEnc <- paheEnc pk cs
              rsEnc <- paheEnc pk rs


              (gamma,()) <-
                  measureTimeSingle "SecureCompare" $
                  concurrently
                  (secureCompareClient req pk eCtx l csEnc rsEnc)
                  (secureCompareServer rep sk l)

              result <- paheDec sk gamma
              unless (map (==1) result == expected) $ do
                  print cs
                  print rs
                  putTextLn $ "Expected: " <> show expected
                  putTextLn $ "Got:      " <> show result
                  error "Mismatch"

              putTextLn "Starting the protocol"
              (eps,()) <-
                  measureTimeSingle "DGKcomp" $
                  concurrently
                  (dgkClient req pk eCtx l rs)
                  (dgkServer rep sk l cs)

              res <- map (== 1) <$> paheDec sk eps
              unless (res == expected) $ do
                  print cs
                  print rs
                  putTextLn $ "Expected: " <> show expected
                  putTextLn $ "Got:      " <> show result
                  error "Mismatch"

      testLogArgmax
