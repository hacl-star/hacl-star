-- | Implementation of argmax protocol

module Argmax where

import Universum

import Control.Concurrent (threadDelay, withMVar)
import Control.Concurrent.Async (concurrently)
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

getCurrentTimeMs :: IO Integer
getCurrentTimeMs = floor . (*1000) <$> getPOSIXTime

lMVar :: MVar ()
lMVar = unsafePerformIO $ newMVar ()

log :: MonadIO m => Text -> m ()
log x = do
    t <- liftIO getCurrentTimeMs
    liftIO $ withMVar lMVar $ \() -> putTextLn (show t <> " " <> x) >> pure ()

shuffle :: [a] -> IO [a]
shuffle [] = pure []
shuffle xs = do
    let l = length xs
    let accum used current j = if j == l then pure current else do
          ix <- randomRIO (0,l-1) `L.suchThat` (\i -> not $ S.member i used)
          accum (S.insert ix used) ((xs !! ix):current) (j+1)
    accum S.empty [] 0


-- Compute r <= c jointly. Client has r, server has c.
dgkClient :: Pahe s => Socket Req -> PahePk s -> Int -> [Integer] -> IO (PaheCiph s)
dgkClient sock pk l rs = do
    threadDelay 100000

    let k = paheK pk
    log "Client: dgk started"
    send sock [] "init"

    let rbits = map (\i -> map (\c -> bool 0 1 $ testBit c i) rs) [0..l-1]
   -- log $ "Client rbits: " <> show rbits
    encRBits <- mapM (paheEnc pk) rbits

    cs <- mapM (paheFromBS pk) =<< receiveMulti sock
    log "Client: dgk main body"

    enczero <- paheEnc pk $ replicate k 0
    encone <- paheEnc pk $ replicate k 1

    xors <- forM (cs `zip` [0..]) $ \(ci,i) -> do
        let bitmask = rbits !! i
        let bitmaskNeg = map (\x -> 1 - x) bitmask

        -- ci * maskNeg + (1-ci) * mask
        a <- paheSIMDMulScal pk ci bitmaskNeg
        oneMinCi <- paheSIMDSub pk encone ci
        c <- paheSIMDMulScal pk oneMinCi bitmask
        paheSIMDAdd pk a c

    delta <- replicateM k (randomRIO (0,1))
    deltaEnc <- paheEnc pk delta
    let s0 = map (\i -> 1 - 2 * i) delta
    --log $ "Client: s = " <> show s0
    s <- paheEnc pk s0


    ci <- forM [0..l-1] $ \i -> do
        a <- paheSIMDAdd pk s (encRBits !! i)
        b <- paheSIMDSub pk a (cs !! i)

        if i == l-1 then pure b else do
            xorsum <- foldrM (paheSIMDAdd pk) enczero $ map (xors !!) [i+1..l-1]
            xorsum3 <- paheSIMDMulScal pk xorsum $ replicate k 3
            paheSIMDAdd pk b xorsum3

    xorsumFull <- foldrM (paheSIMDAdd pk) enczero xors
    xorsumFull3 <- paheSIMDMulScal pk xorsumFull $ replicate k 3
    cLast <- paheSIMDAdd pk deltaEnc xorsumFull3

    ciShuffled <- shuffle =<< mapM (paheMultBlind pk) (cLast : ci)

    sendMulti sock =<< (NE.fromList <$> mapM (paheToBS pk) ciShuffled)

    zs <- paheFromBS pk =<< receive sock

    let compeps = do
          let sMask = map (bool 1 0 . (== 1)) s0
          let sMaskNeg = map (\x -> 1 - x) sMask
          -- zs * s + (1-zs) * neg s
          a <- paheSIMDMulScal pk zs sMask
          oneMinZs <- paheSIMDSub pk encone zs
          c <- paheSIMDMulScal pk oneMinZs sMaskNeg
          paheSIMDAdd pk a c

    eps <- compeps

    log "Client: dgk ended"
    pure eps

dgkServer :: Pahe s => Socket Rep -> PaheSk s -> Int -> [Integer] -> IO ()
dgkServer sock sk l cs = do
    let pk = paheToPublic sk
    let k = paheK pk

    let cbits = map (\i -> map (\c -> bool 0 1 $ testBit c i) cs) [0..l-1]
--    log $ "Server cbits: " <> show cbits

    _ <- receive sock
    log "Server: dgk started"

    sendMulti sock =<< (NE.fromList <$> mapM (paheToBS pk <=< paheEnc pk) cbits)

    es <- mapM (paheFromBS pk) =<< receiveMulti sock
    log "Server: dgk computing zeroes"
    esDecr <- mapM (paheDec sk) es
    let zeroes = map (bool 1 0 . (== 0)) $
                 foldr (\e acc -> map (uncurry (*)) $ zip e acc)
                       (replicate k 1) esDecr
    log $ "Server: zeroes " <> show zeroes

    enczeroes <- paheEnc pk zeroes
    send sock [] =<< paheToBS pk enczeroes

    log "Server: dgk exited"


-- Compute y <= x jointly with secret inputs. Client has r, server has c.
secureCompareClient ::
       Pahe s
    => Socket Req
    -> PahePk s
    -> Int
    -> PaheCiph s
    -> PaheCiph s
    -> IO (PaheCiph s)
secureCompareClient sock pk l x y = do
    log "Client: secureCompare started"
    let k = paheK pk

    rhos::[Integer] <- replicateM k $ randomRIO (0, 2^(l + 80))
    s0 <- paheEnc pk (map (+(2^l)) rhos)
    s1 <- paheSIMDAdd pk s0 x
    gamma <- paheSIMDSub pk s1 y

    log "Client: secureCompare blinded, sent to server"
    send sock [] =<< paheToBS pk gamma

    cDiv2l <- paheFromBS pk =<< receive sock

    log "Client: secureCompare, running dgk"
    eps <- dgkClient sock pk l $ map (`mod` (2^l)) rhos

    oneEnc <- paheEnc pk $ replicate k 1
    epsNeg <- paheSIMDSub pk oneEnc eps

    rDiv2 <- paheEnc pk $ map (`div` (2^l)) rhos
    rPlusEpsNeg <- paheSIMDAdd pk rDiv2 epsNeg
    delta <- paheSIMDSub pk cDiv2l rPlusEpsNeg

    --deltaDec <- paheDec sk delta
    --xDec <- (!! 0) <$> paheDec sk x
    --yDec <- (!! 0) <$> paheDec sk y
    --unless (deltaDec !! 0 == ((2^l) + xDec - yDec) `div` (2^l)) $ do
    --    print xDec
    --    print yDec
    --    print =<< paheDec sk eps
    --    print =<< paheDec sk epsNeg
    --    print =<< paheDec sk cDiv2l
    --    print deltaDec
    --    print $ map (`div` (2^l)) rhos
    --    error "SecureCompare is broken"

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

    log "Server: securecompare decoded blinded msg, running dgk"
    dgkServer sock sk l cMod2

w64ToBs :: Word64 -> ByteString
w64ToBs = BS.pack . map fromIntegral . inbase 256 . fromIntegral

w64FromBs :: ByteString -> Word64
w64FromBs = fromIntegral . frombase 256 . map fromIntegral . BS.unpack

argmaxClient ::
       Pahe s
    => Socket Req
    -> PaheSk s
    -> PahePk s
    -> Int
    -> [PaheCiph s]
    -> IO (PaheCiph s, [Word64])
argmaxClient sock sk pk l vals = do
    let k = paheK pk
    let m = length vals
    perm <- shuffle [0..m-1]
    log $ "Perm: " <> show perm

    oneEnc <- paheEnc pk $ replicate k 1
    let loop curMax i = if i == m then pure curMax else do
            log $ "Client loop index " <> show i
            bi <- secureCompareClient sock pk l
                (vals !! (perm !! i)) curMax
            ri <- replicateM k $ randomRIO (0, 2^(l + 80))
            si <- replicateM k $ randomRIO (0, 2^(l + 80))
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

            newMaxDec <- paheDec sk newMax
            log $ "Client, new max: " <> show newMaxDec

            loop newMax (i+1)

    startMaxVal <- paheDec sk (vals !!(perm !! 0))
    log $ "Client, start max: " <> show startMaxVal
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

    let loop index i = if i == m then pure index else do
            log $ "Server loop index " <> show i
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

            let index' =
                    map (\j -> if bi !! j == 1 then i else index !! j) [0..k-1]
            log "Server loop end"
            loop index' (i+1)

    index <- loop (replicate k 0) 1
    log $ "Server: argmax loop ended, indices: " <> show index

    _ <- receive sock
    sendMulti sock $ NE.fromList $ map (w64ToBs . fromIntegral) index

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
      let k = 8
      sk <- paheKeyGen @PailSep k
      let pk = paheToPublic sk

      let testArgmax = replicateM_ 1 $ do
              let l = 5
              let m = 6
              vals <- replicateM m $ replicateM k $ randomRIO (0,2^l-1)
              print vals
              let expected = foldr1 (\l1 l2 -> map (uncurry max) $ zip l1 l2) vals
              encVals <- mapM (paheEnc pk) vals

              ((maxes,indices),()) <- concurrently
                  (argmaxClient req sk pk l encVals)
                  (argmaxServer rep sk l m)

              putTextLn "Maxes/indices"
              decMaxes <- paheDec sk maxes
              print decMaxes
              print indices

              if (decMaxes /= expected)
                  then error "Argmax failed" else putTextLn "OK"

      testArgmax

      let testCompare = replicateM_ 10 $ do
              let l = 5
              cs <- replicateM k $ randomRIO (0,2^l-1)
              rs <- replicateM k $ randomRIO (0,2^l-1)
              print cs
              print rs
              let expected = map (\(c,r) -> r <= c) $ zip cs rs

              csEnc <- paheEnc pk cs
              rsEnc <- paheEnc pk rs


              (gamma,()) <- concurrently
                  (secureCompareClient req pk l csEnc rsEnc)
                  (secureCompareServer rep sk l)

              result <- paheDec sk gamma
              unless (map (==1) result == expected) $ do
                  print cs
                  print rs
                  putTextLn $ "Expected: " <> show expected
                  putTextLn $ "Got:      " <> show result
                  error "Mismatch"

              --putTextLn "Starting the protocol"
              --(eps,()) <- concurrently
              --  (dgkClient req pk l rs)
              --  (dgkServer rep sk l cs)

              --result <- map (== 1) <$> paheDec sk eps
              --unless (result == expected) $ do
              --    print cs
              --    print rs
              --    putTextLn $ "Expected: " <> show expected
              --    putTextLn $ "Got:      " <> show result
              --    error "Mismatch"

      putTextLn "Protocol exited"
