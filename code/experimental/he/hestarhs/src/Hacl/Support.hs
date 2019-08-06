-- | Methods to support PAHE, like key generation, packing modes, etc.

module Hacl.Support where

import Universum hiding (exp, last, (<*>))

import System.Random (randomIO, randomRIO)

import Lib hiding (crt)


genPrime :: Int -> IO Integer
genPrime bits = do
    p <- randomRIO (2 ^ (bits - 4),2 ^ bits)
    --if isPrime p
    if isPrimeMR 40 p
      then pure p else genPrime bits


legendreSymbol :: Integer -> Integer -> Integer
legendreSymbol p a = let res = exp p a ((p-1) `div` 2) in if res == p-1 then (-1) else res

genDataGM :: Int -> IO (Integer,Integer,Integer,Integer,Bool,Bool)
genDataGM bits = do
    let genPrimes = do
            p <- genPrime (bits `div` 2)
            q <- genPrime (bits `div` 2)
            if p == q then genPrimes else pure (p,q)
    (p,q) <- genPrimes
    let n = p * q
    let genY = do
            y <- randomRIO (2^(bits-2), n-1)
            if legendreSymbol p y == -1 && legendreSymbol q y == -1
               then pure y
               else genY
    y <- genY
    let genR = do
            r <- randomRIO (2^(bits-2), n-1)
            if (r * r) `mod` n > 0 && (r * r * y) `mod` n > 0 then pure r else genR
    r <- genR
    m1 <- randomIO
    m2 <- randomIO
    return (p,q,y,r,m1,m2)


genDataPaillier :: Int -> IO (Integer,Integer,Integer,Integer,Integer)
genDataPaillier bits = do
    let genPrimes = do
            p <- genPrime (bits `div` 2)
            q <- genPrime (bits `div` 2)
            if p == q then genPrimes else pure (p,q)
    (p,q) <- genPrimes
    let n = p * q
    let genR = do
            r <- randomRIO (0,n-1)
            if gcd r n == 1 then pure r else genR
    r <- genR
    m1 <- randomRIO (0,n-1)
    m2 <- randomRIO (0,n-1)
    return (p,q,r,m1,m2)
