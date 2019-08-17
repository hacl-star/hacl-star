module Main where

import Universum

import Control.Concurrent (threadDelay)
import qualified Control.Concurrent.Async as A
import System.ZMQ4

import Argmax
import Comparison
import Hacl
import Hacl.Packing
import Playground
import TestHacl
import Utils


measureDelay :: Socket Req -> Socket Rep -> IO ()
measureDelay req rep = do
    putTextLn "Measuring delay"

    let tries = 100

    let server = replicateM tries $ do
            e <- receive rep
            send rep [] ""
            mcstime2 <- getCurrentTimeMcs
            putTextLn "."
            let delta =(mcstime2 - fromIntegral (w64FromBs e))
            pure delta

    let client = replicateM_ tries $ do
            mcstime <- getCurrentTimeMcs
            send req [] (w64ToBs $ fromIntegral mcstime)
            void $ receive req


    ((),xs) <- A.concurrently client server
    putTextLn $ "Average latency is: " <> show (average xs) <> "mcs"


lanLoopback :: IO ()
lanLoopback =
    withContext $ \ctx ->
    withSocket ctx Req $ \req ->
    withSocket ctx Rep $ \rep -> do
      putTextLn "Initialised the context, generating params"
      -- USB
      --bind rep "tcp://192.168.42.86:8875"
      --connect req "tcp://192.168.42.129:8875"
      ---- WAN teth
      --bind rep "tcp://192.168.43.225:8875"
      --connect req "tcp://192.168.43.53:8875"

      -- WAN global
      bind rep "tcp://192.168.88.253:8875"
      connect req "tcp://192.168.88.249:8875"


      measureDelay req rep

      putTextLn "waiting..."

      _testArgmax req rep


benchCrypto :: IO ()
benchCrypto = do
    benchBNs 512
    benchBNs 1024
    benchBNs 2048
    testGM 512
    testGM 1024
    testGM 2048
    testPaillier 512
    testPaillier 1024
    testPaillier 2048
    testDGK 1 193 512
    testDGK 1 193 1024
    testDGK 1 193 2048




main :: IO ()
main = do
    --runProtocol
    --testDGK
    --_testArgmax
    --_testCmp
    --testDGKPahe
    --lanLoopback
    _testCmpFull
    --benchCrypto
    --benchCRTs
    --testDGKPaheCriterion
