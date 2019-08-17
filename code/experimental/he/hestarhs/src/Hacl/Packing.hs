{-# LANGUAGE NamedFieldPuns #-}
-- | Packing methods

module Hacl.Packing where

import Universum hiding (exp, last, (<*>))

import Criterion.Main
import Data.List ((!!))
import Data.Vector (Vector, (!))
import qualified Data.Vector as V
import System.Random (randomRIO)

import Hacl.Bignum
import Hacl.Raw
import Lib
import Utils

----------------------------------------------------------------------------
-- CRT packing
----------------------------------------------------------------------------

singlesOut :: [Integer] -> Int -> Maybe Int
singlesOut [1] i    = Just i
singlesOut (0:xs) i = singlesOut xs (i+1)
singlesOut _ _      = Nothing

crt :: [Integer] -> [Integer] -> [Integer] -> Integer
crt _ _ [] = 0
crt allbase@(m1:base) (tp0:tailProds) el@(a1:vals) =

    case singlesOut el 0 of
      Nothing -> chineseGo base tailProds  vals (a1 `mod` m1) m1
      Just i ->
          let mi = allbase !! i in
          let bi = tp0 `div` mi in
          bi * (inverse bi mi)
  where
    chineseGo :: [Integer] -> [Integer] -> [Integer] -> Integer -> Integer -> Integer
    chineseGo [] _ _ c _ = c
    chineseGo (_:_) (tProd:_) [] c mprod = c'
        where
          m' = inverse mprod tProd
          y = (- m' * c) `mod` tProd
          c' = c + mprod * y
    chineseGo (m:xs1) (_:tpds) (a:xs2) c mprod =
        chineseGo xs1 tpds xs2 c' (mprod * m)
        where
          m' = inverseP mprod m
          y = (m' * (a - c)) `mod` m
          c' = c + mprod * y
    chineseGo _ _ _ _ _ = error "chineseGo pattern match failed"
crt [] _ _ = error "crt base is empty"
crt _ [] _ = error "crt tailprods is empty"

compTailProds :: [Integer] -> [Integer]
compTailProds [] = error "compTailProds empty"
compTailProds xs = go xs
  where
    go []     = []
    go (a:as) = product (a:as) : go as

crtInv :: [Integer] -> Integer -> [Integer]
crtInv base v = map (v `mod`) base

crtToBase :: [Integer] -> [Integer] -> [Integer]
crtToBase base vals = map (\(b,p) -> b `mod` p) $ vals `zip` base



crtVec :: Vector Integer -> Vector Integer -> [Integer] -> Integer
crtVec base tailProds (a0:vals) =
    let m = V.head base in
    chineseGo 1 vals (a0 `mod` m) m
  where
    chineseGo :: Int -> [Integer] -> Integer -> Integer -> Integer
    chineseGo j _ c _ | j == V.length base = c
    chineseGo i [] c mprod = c'
        where
          tpcur = tailProds ! (i-1)
          m' = inverse mprod tpcur
          y = (- m' * c) `mod` tpcur
          c' = c + mprod * y
    chineseGo i (a:as) c mprod =
        chineseGo (i+1) as c' (mprod * m)
        where
          m = base ! i
          m' = inverse mprod m
          y = (m' * (a - c)) `mod` m
          c' = c + mprod * y
crtVec _ _ _ = error "crt lists are too empty"


crtInvVec :: Vector Integer -> Integer -> [Integer]
crtInvVec base v = map (\i -> v `mod` base ! i) [0..V.length base-1]


crtToBaseVec :: Vector Integer -> [Integer] -> [Integer]
crtToBaseVec base vals =
    map (\(b,i) -> b `mod` base ! i) $ vals `zip` [0..V.length base - 1]



crtC :: Word32 -> Int -> BignumList -> [Integer] -> [Integer] -> IO Bignum
crtC bn l _ (p0:_) vals | l == 1 =
    toBignum bn $ case vals of
                    []    -> 0
                    (x:_) -> x `mod` p0
crtC bn l ps base vals = do
--    putTextLn $ "crtC 1: " <> show (bn, l, length base, length vals)
    res <- toBignumZero bn
--    putTextLn "crtC 2"
    as <- toBignumList bn l $ crtToBase base vals
--    putTextLn "crtC 3"
    osslCRT bn (fromIntegral l) ps as res
--    putTextLn "crtC 4"
    pure res

testCrtC :: IO ()
testCrtC = do
    let bn = 64
    let n = 1
    let bound = 32
    let prms = genConsecutivePrms n bound
    bnl_prms <- toBignumList bn n prms

    replicateM_ 1000 $ do
        m <- randomRIO (1,n)
        vs <- replicateM m $ randomRIO (0,bound-1)
        enc <- crtC bn n bnl_prms prms vs
        dec <- crtInv prms <$> fromBignum bn enc
        unless (dec == vs ++ replicate (n-m) 0) $ do
            print vs
            print dec
            error "crt is broken"



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

    measureTimeSingle "crt" $ replicateM_ 10000 $ do
        m <- randomRIO (1,n)
        vs <- (++ [1]) <$> replicateM (m-1) (pure 0) --  $ randomRIO (0,bound-1)
        let tprods = compTailProds prms
        let enc = crt prms tprods vs
        let dec = crtInv prms enc
        unless (dec == vs ++ replicate (n-m) 0) $ do
            print vs
            print dec
            error "crt is broken"


testCRTVec :: IO ()
testCRTVec = do
    let n = 8
    let bound = 32
    let prms = genConsecutivePrms n bound

    measureTimeSingle "crt" $ replicateM_ 10000 $ do
        m <- randomRIO (1,n)
        vs <- replicateM m $ randomRIO (0,bound-1)
        let tprods = compTailProds prms
        let enc = crtVec (V.fromList prms) (V.fromList tprods) vs
        let dec = crtInv prms enc
        unless (dec == vs ++ replicate (n-m) 0) $ do
            print vs
            print dec
            error "crt is broken"

-- No big difference observed
benchCRTs :: IO ()
benchCRTs = defaultMain $ [
    env (genTopEnv 32) (\ ~(prms, prmsTail, prmsV, prmsTailV) ->
      bgroup "k = 32"
        [ bench "CRT List 1" $ perRunEnv (genEnv 1) $ \(x::[Integer]) ->
             pure $ crt prms prmsTail x
        , bench "CRT List 1 toBignum" $ perRunEnv (genEnv 1) $ \(x::[Integer]) ->
             toBignum 64 $ crt prms prmsTail x
        , bench "CRT List 32" $ perRunEnv (genEnv 32) $ \(x::[Integer]) ->
             pure $ crt prms prmsTail x
        , bench "CRT List 32 toBignum" $ perRunEnv (genEnv 32) $ \(x::[Integer]) ->
             toBignum 64 $ crt prms prmsTail x
        , bench "CRT Vector 1" $ perRunEnv (genEnv 1) $ \(x::[Integer]) ->
             pure $ crtVec prmsV prmsTailV x
        , bench "CRT Vector 32" $ perRunEnv (genEnv 32) $ \(x::[Integer]) ->
             pure $ crtVec prmsV prmsTailV x
        ]),
    env (genTopEnv 1) (\ ~(prms, prmsTail, prmsV, prmsTailV) ->
      bgroup "k = 1"
        [ bench "CRT List 1" $ perRunEnv (genEnv 1) $ \(x::[Integer]) ->
             pure $ crt prms prmsTail x
        , bench "CRT List 1 toBignum" $ perRunEnv (genEnv 1) $ \(x::[Integer]) ->
             toBignum 64 $ crt prms prmsTail x
        , bench "CRT Vector 1" $ perRunEnv (genEnv 1) $ \(x::[Integer]) ->
             pure $ crtVec prmsV prmsTailV x
        ])

    ]
  where
    bound = 32
    genTopEnv n = do
        let prms = genConsecutivePrms n bound
        let prmsTail = compTailProds prms
        let prmsV = V.fromList prms
        let prmsTailV = V.fromList prmsTail
        pure (prms, prmsTail, prmsV, prmsTailV)

    genEnv :: Int -> IO [Integer]
    genEnv m = replicateM m $ randomRIO (0,bound-1)

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
