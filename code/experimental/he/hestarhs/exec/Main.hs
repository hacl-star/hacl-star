module Main where

import Universum

import Control.Concurrent (threadDelay)
import qualified Control.Concurrent.Async as A
import System.IO (hFlush, stdout)
import System.ZMQ4

import Argmax
import Comparison
import Hacl
import Hacl.Packing
import Playground
import TestHacl
import Utils


measureDelay :: Socket Dealer -> Socket Dealer -> IO ()
measureDelay req rep = do
    putTextLn "Measuring delay"

    let tries = 300

    let server = replicateM tries $ do
            e <- zreceive rep
            zsend rep ""
            mcstime2 <- getCurrentTimeMcs
            let delta =(mcstime2 - fromIntegral (w64FromBs e))
            putText "."
            hFlush stdout
            pure delta

    let client = replicateM_ tries $ do
            mcstime <- getCurrentTimeMcs
            zsend req (w64ToBs $ fromIntegral mcstime)
            void $ zreceive req


    ((),xs) <- A.concurrently client server
    putTextLn $ "Average latency is: " <> show (average xs) <> "mcs"


lanLoopback :: IO ()
lanLoopback =
    withContext $ \ctx ->
    withSocket ctx Dealer $ \req ->
    withSocket ctx Dealer $ \rep -> do
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

      --_testCmp 1 req rep
      --_testCmp 8 req rep
      --_testCmp 16 req rep

      _testArgmax 4 req rep
      measureDelay req rep
      _testArgmax 8 req rep
      measureDelay req rep
      _testArgmax 16 req rep


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
    lanLoopback
    --benchCrypto
    --benchCRTs
    --testDGKPaheCriterion
    --_testCmpInproc 1
    --_testCmpInproc 8
    --_testCmpInproc 16
    --_testArgmaxInproc 4
    --_testArgmaxInproc 8
    --_testArgmaxInproc 16
    --_testArgmaxInproc 16
