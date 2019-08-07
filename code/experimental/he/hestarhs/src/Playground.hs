{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

-- | Smth.

module Playground where

import Universum hiding (exp, last, (<*>))

import Data.List (delete, last, (!!))
import Data.Numbers.Primes (primeFactors, primes)
import System.Random (randomIO, randomRIO)

import Hacl
import Lib hiding (crt)


isMthPrimRoot :: Integer -> Integer -> Integer -> Bool
isMthPrimRoot n m w = go w m
  where
    go acc pow = if pow == 1 then acc == 1 else acc /= 1 && go ((acc * w) `mod` n) (pow-1)

findMthPrimRoot :: Integer -> Integer -> Maybe Integer
findMthPrimRoot n m = find (isMthPrimRoot n m) [0..n-1]

testFindPrimRoot :: IO ()
testFindPrimRoot = do
    let s = 128
    let genPrimes i = do
            p <- genPrime 20
            q <- genPrime 20
            let lam = lcm (p-1) (q-1)
            if lam `mod` s == 0
               -- && isPrime (lam `div` s)
                then pure (p,q,i) else genPrimes (i+1)
    (p,q,i) <- genPrimes 0
    putTextLn $ "Iteration: " <> show i
    let n = p * q
    let lam = lcm (p-1) (q-1)
    let lamFactors = ordNub $ 1024 : primeFactors (lam `div` 1024)

    let isGen g =
            gcd g n == 1 &&
            all (\factor -> exp n g factor /= 1) lamFactors &&
            exp n g lam == 1

    let tryGen j = if i == 0 then pure Nothing else do
            let lroot :: Integer = fromMaybe (error "should work") $ find isGen [1..]
            let mroot = exp n lroot (lam `div` s)
            if isMthPrimRoot n 4 mroot then pure (Just mroot) else tryGen (j-1)

    tryGen 10 >>= \case
        Nothing -> testFindPrimRoot
        Just mroot -> putTextLn $ show mroot

carm :: Integer -> Integer
carm x =
    let fs = primeFactors x in
    let fsn = ordNub fs in
    case fsn of
      [_] -> fromIntegral $
          if (length fs > 2) then eulerPhiFast x `div` 2 else eulerPhiFast x
      xs  -> foldr1 lcm $ map carm xs
