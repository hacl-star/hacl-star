module Main where

import Universum

import qualified Foreign.Marshal.Alloc as A
import Hacl


inbase :: Integer -> Integer -> [Integer]
inbase base i = i `mod` base : inbase base (i `div` base)


main :: IO ()
main = do
    a <- A.mallocBytes 16
    b <- A.mallocBytes 16
    c <- A.mallocBytes 16
    bn_sub 2 2 a b c
