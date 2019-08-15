module Main where

import Universum

import Control.Concurrent (threadDelay)
import qualified Control.Concurrent.Async as A
import System.ZMQ4

import Argmax
import Comparison
import Hacl
import Playground
import TestHacl
import Utils


lanLoopback :: IO ()
lanLoopback =
    withContext $ \ctx ->
    withSocket ctx Req $ \req ->
    withSocket ctx Rep $ \rep -> do
      putTextLn "Initialised the context, generating params"
      bind rep "tcp://192.168.42.86:8875"
      connect req "tcp://192.168.42.129:8875"

      putTextLn "waiting..."

      _testArgmax req rep

--      let server = forever $ do
--              [_,e] <- receiveMulti rep
--              mstime2 <- getCurrentTimeMs
--              log $ "Server: received: " <> show (mstime2 - fromIntegral (w64FromBs e))
--
--      let client = forM_ [0..] $ \i -> do
--              mstime <- getCurrentTimeMs
--              log $ "client: pinging " <> show i
--              send req [] (w64ToBs $ fromIntegral mstime)
--              threadDelay 1000000
--
--
--      void $ A.concurrently client server



main :: IO ()
main = do
    --runProtocol
    --testDGK
    --_testArgmax
    --_testCmp
    --testDGKPahe
    lanLoopback
