{-# LANGUAGE NamedFieldPuns #-}
-- | Packing methods

module Hacl.Packing where

import Universum hiding (exp, last, (<*>))

import System.Random (randomRIO)

import Lib
import Utils

----------------------------------------------------------------------------
-- CRT packing
----------------------------------------------------------------------------


crt :: [Integer] -> [Integer] -> Integer
crt (m1:base) (a1:vals) = chineseGo base vals (a1 `mod` m1) m1
  where
    chineseGo :: [Integer] -> [Integer] -> Integer -> Integer -> Integer
    chineseGo [] _ c _ = c
    chineseGo bleft [] c mprod = chineseGo [product bleft] [0] c mprod
    chineseGo (m:xs1) (a:xs2) c mprod =
        chineseGo xs1 xs2 c' (mprod * m)
        where
          m' = inverse mprod m
          y = (m' * ((a - c) `mod` m)) `mod` m
          c' = c + mprod * y
crt _ _ = error "crt lists are too empty"


crtInv :: [Integer] -> Integer -> [Integer]
crtInv base v = map (v `mod`) base

crtToBase :: [Integer] -> [Integer] -> [Integer]
crtToBase base vals = map (\(b,p) -> b `mod` p) $ vals `zip` base

genConsecutivePrms :: Int -> Integer -> [Integer]
genConsecutivePrms n bound =
    reverse $ go 0 [] (if even bound then bound+1 else bound+2)
  where
    go l xs toTest = if l >= n then xs else
        if isPrimeMR 40 toTest
        then go (l+1) (toTest:xs) (toTest+2)
        else go l xs (toTest+2)

testCRT :: IO ()
testCRT = do
    let n = 8
    let bound = 32
    let prms = genConsecutivePrms n bound

    measureTimeSingle "crt" $ replicateM_ 1000 $ do
        m <- randomRIO (1,n-1)
        vs <- replicateM m $ randomRIO (0,bound-1)
        let enc = crt prms vs
        let dec = crtInv prms enc
        unless (dec == vs ++ replicate (n-m) 0) $ do
            print vs
            print dec
            error "crt is broken"

----------------------------------------------------------------------------
-- DFT Packing is in the playground.hs
----------------------------------------------------------------------------

data DFTParams =
    DFTParams
        {
          djm    :: Integer
        , djN    :: Integer
        , djw    :: Integer
        , djwInv :: Integer -- modulo N
        , djn    :: Integer
        , djnInv :: Integer -- modulo N
        , djU    :: Integer
        , dju    :: Integer -- slot size, such that U = u ^ n -1
        } deriving (Show)

-- finds prime k * n + 1 that it's more than m
genDFTModulus :: Integer -> Integer -> (Integer,Integer)
genDFTModulus n m = go (m `div` n + 1)
  where
    go k = if isPrimeMR 40 (k*n + 1) then (k, k*n+1) else go (k + 1)

-- Finds generator of multiplicative group of Z_n
findGen :: Integer -> Integer
findGen n =
    fromMaybe (error $ "findGenerator: didn't manage to, the group is not cyclic") $
    find (\g -> order n g == Just (n-1)) [1..n-1]

findDFTRoot :: Integer -> Integer -> Integer
findDFTRoot k djN = exp djN (findGen djN) k

genDFTParams :: Integer -> Integer -> Integer -> DFTParams
genDFTParams djn djm slotBits =
    let (k, djN) = genDFTModulus djn djm in
    let djw = findDFTRoot k djN in
    let djwInv = inverse djw djN in
    let djnInv = inverse djn djN in
    let dju = djN * (2 ^ slotBits) in -- N + extra bits required
    let djU = dju ^ djn - 1 in
    DFTParams {..}

dftRaw :: Integer -> Integer -> Integer -> [Integer] -> [Integer]
dftRaw djN n w ax = map (\j -> dotprod (row j) ax) [0..n-1]
  where
    row1 = map (\i -> exp djN w i) [0..n-1]
    row :: Integer -> [Integer]
    row i = map (\wi -> exp djN wi i) row1

dft :: DFTParams -> [Integer] -> [Integer]
dft DFTParams{..} = dftRaw djN djn djw

dftinv :: DFTParams -> [Integer] -> [Integer]
dftinv DFTParams {..} =
    map (\x -> (djnInv * x) `mod` djN) .
    dftRaw djN djn djwInv
