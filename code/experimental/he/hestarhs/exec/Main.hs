module Main where

import Universum

import Argmax
import Hacl
import Playground
import TestHacl


main :: IO ()
main = do
    --runProtocol
    testDGK
    --print =<< genDataDGKWithPrimes 1 (2^8) 1024
