module Main where

import Universum

import Playground
import TestHacl



main :: IO ()
main = do
    print =<< genDataDGK [(31,1)] 512
    print =<< genDataDGK [(31,1)] 1024
    print =<< genDataDGK [(31,1)] 2048
    --testPaillier
