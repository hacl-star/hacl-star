module Main where

import Universum

import Argmax
import Playground


main :: IO ()
main = do
    runProtocol
    --print =<< genDataDGK [(31,1)] 512
    --print =<< genDataDGK [(31,1)] 1024
    --print =<< genDataDGK [(31,1)] 2048
