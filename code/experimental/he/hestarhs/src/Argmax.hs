-- | Implementation of argmax protocol

module Argmax where

import Universum

import Control.Concurrent (threadDelay, withMVar)
import Control.Concurrent.Async (concurrently)
import Data.Bits (testBit)
import qualified Data.ByteString as BS
import Data.List ((!!))
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

      replicateM_ 10 $ do
          let l = 5
          cs <- replicateM k $ randomRIO (0,2^l-1)
          rs <- replicateM k $ randomRIO (0,2^l-1)
          let expected = map (\(c,r) -> r <= c) $ zip cs rs

          putTextLn "Starting the protocol"
          -- Compute r <= c jointly. Client has r, server has c
          -- or r < c.
          (eps,()) <- concurrently
            (dgkClient req pk l rs)
            (dgkServer rep sk l cs)

          result <- map (== 1) <$> paheDec sk eps
          unless (result == expected) $ do
              print cs
              print rs
              putTextLn $ "Expected: " <> show expected
              putTextLn $ "Got:      " <> show result
              error "Mismatch"

      putTextLn "Protocol exited"
