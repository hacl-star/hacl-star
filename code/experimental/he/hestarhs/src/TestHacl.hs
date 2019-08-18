module TestHacl where

import Universum

import Control.DeepSeq (rnf2)
import Criterion.Main
import qualified Data.Time.Clock.POSIX as P
import System.Random (randomIO, randomRIO)

import Hacl
import qualified Lib as L
import Utils

testBNs :: IO ()
testBNs = do
    let bitl = 1024
    n <- genPrime bitl
    let bn = fromIntegral $ length $ inbase b64 n
    a <- randomRIO (0,n`div`2)
    b <- randomRIO (0,n`div`2)
    putTextLn $ "n: " <> show n
    putTextLn $ "a: " <> show a
    putTextLn $ "a2: " <> show (a*a)
    putTextLn $ "b: " <> show b
    putTextLn $ "(a+b) mod n: " <> show (a+b)
    putTextLn $ "a^b mod n: " <> show (L.exp n a b)

    bnN <- toBignum bn n
    bnA <- toBignum bn a
    bnB <- toBignum bn b
    res <- toBignum bn 0

    bnModExp bn bn bnN bnA bnB res
    expRes <- fromBignum bn res

    putTextLn $ "expRes: " <> show expRes
    print $ expRes == (L.exp n a b)

    bsB <- fromBignumBS bn bnB
    bnBBack <- fromBignum bn =<< toBignumBS bn bsB
    unless (bnBBack == b) $ error "decoding failed"


benchBNs :: Int -> IO ()
benchBNs bitl = do
    putTextLn $ "Testing bignums, len: " <> show bitl

    let doTest = do
          n <- genPrime bitl
          let bn0 = fromIntegral $ length $ inbase b64 n
          let bn = bn0 + 1

          let attempts = 100

          a <- randomRIO (0,n-1)
          b <- randomRIO (0,n-1)
          c <- randomRIO (0,a-1)

          s1 <- randomRIO (0,2^(bitl`div`3))
          s2 <- randomRIO (0,2^(bitl`div`3))

          bnN <- toBignum bn n
          bnA <- toBignum bn a
          bnB <- toBignum bn b
          bnC <- toBignum bn c
          res <- toBignum bn 0
          bnS1 <- toBignum bn s1
          bnS2 <- toBignum bn s2

          time0 <- P.getPOSIXTime

          replicateM_ attempts $ bnRemainder bn bn bnA bnC res

          time1 <- P.getPOSIXTime

          replicateM_ attempts $ bnModAdd bn bnN bnA bnB res

          time2 <- P.getPOSIXTime

          replicateM_ attempts $ bnModMul bn bnN bnA bnB res

          time3 <- P.getPOSIXTime

          replicateM_ attempts $ bnMulFitting bn bn bn bnS1 bnS2 res

          time4 <- P.getPOSIXTime

          replicateM_ attempts $ bnModExp bn bn bnN bnA bnB res

          time5 <- P.getPOSIXTime

          pure ( (time1 - time0) / fromIntegral attempts
               , (time2 - time1) / fromIntegral attempts
               , (time3 - time2) / fromIntegral attempts
               , (time4 - time3) / fromIntegral attempts
               , (time5 - time4) / fromIntegral attempts)


    let tries = 50
    timings <- replicateM tries doTest

    let average xs = foldr1 (+) xs / fromIntegral tries
    let avg1 = average $ map (view _1) timings
    let avg2 = average $ map (view _2) timings
    let avg3 = average $ map (view _3) timings
    let avg4 = average $ map (view _4) timings
    let avg5 = average $ map (view _5) timings


    putTextLn $ "Mod: "    <> show (avg1 * 1000000) <> " mcs"
    putTextLn $ "ModAdd: " <> show (avg2 * 1000000) <> " mcs"
    putTextLn $ "ModMul: " <> show (avg3 * 1000000) <> " mcs"
    putTextLn $ "MulFit: " <> show (avg4 * 1000000) <> " mcs"
    putTextLn $ "ModExp: " <> show (avg5 * 1000000) <> " mcs"


testGM :: Int -> IO ()
testGM bits = do
    putTextLn $ "Testing GM, bits: " <> show bits


    let test = do
          (p,q,y,r,m1,m2) <- genDataGM bits
          let n = p * q

          let attempts = 1000

          let bN = fromIntegral $ length $ inbase b64 n

          n' <- toBignum bN n
          p' <- toBignum bN p
          y' <- toBignum bN y
          r' <- toBignum bN r
          pmin1 <- toBignum bN (p-1)
          pmin1half <- toBignum bN ((p-1)`div`2)

          c1 <- toBignum bN 0
          c2 <- toBignum bN 0
          c3 <- toBignum bN 0

          let gmSimdMul c b =
                if b then pure c else do
                   res <- toBignum bN 0
                   gmXor bN n' c c res
                   pure res

          (scals::[Bool]) <- replicateM attempts randomIO

          time1 <- P.getPOSIXTime

          replicateM_ (attempts - 1) $ gmEnc bN n' y' r' m1 c1
          gmEnc bN n' y' r' m2 c2

          time2 <- P.getPOSIXTime

          replicateM_ (attempts - 1) $ gmDec bN p' pmin1 pmin1half c1
          m1' <- gmDec bN p' pmin1 pmin1half c1

          time3 <- P.getPOSIXTime

          replicateM_ attempts $ gmXor bN n' c1 c2 c3

          time4 <- P.getPOSIXTime

          forM_ scals $ gmSimdMul c3

          time5 <- P.getPOSIXTime


          when (m1 /= m1') $ error $ "GM failed: " <> show (p,q,y,r,m1,m2)
          pure ( (time2 - time1) / fromIntegral attempts
               , (time3 - time2) / fromIntegral attempts
               , (time4 - time3) / fromIntegral attempts
               , (time5 - time4) / fromIntegral attempts
               )

    let tries = 10
    timings <- replicateM tries test

    let average xs = foldr1 (+) xs / fromIntegral tries
    let avg1 = average $ map (view _1) timings
    let avg2 = average $ map (view _2) timings
    let avg3 = average $ map (view _3) timings
    let avg4 = average $ map (view _4) timings

    putTextLn $ "Enc: " <> show (avg1 * 1000000) <> " mcs"
    putTextLn $ "Dec: " <> show (avg2 * 1000000) <> " mcs"
    putTextLn $ "Add: " <> show (avg3 * 1000000) <> " mcs"
    putTextLn $ "Mul: " <> show (avg4 * 1000000) <> " mcs"

testPahe :: IO ()
testPahe = do
    putTextLn "Testing PAHE"

    let n = 16
    let bound = 64 * 3
    sk <- paheKeyGen @DgkCrt n bound
    let pk = paheToPublic sk

    replicateM_ 100 $ do
        m1Len <- randomRIO (0,n)
        m2Len <- randomRIO (0,n)
        scalLen <- randomRIO (0,n)
        ms1 <- replicateM m1Len $ randomRIO (0, bound-1)
        ms2 <- replicateM m2Len $ randomRIO (0, bound-1)
        scal <- replicateM scalLen $ randomRIO (0, bound-1)


        c1 <- paheEnc pk ms1
        d0 <- paheDec sk c1
        let expectedDec = paheToPlaintext pk ms1
        unless (expectedDec `isPrefixOf` d0) $ do
            print expectedDec
            print d0
            error "Simd dec is broken"

        c2 <- paheEnc pk ms2

        c3 <- paheSIMDAdd pk c1 c2
        d1 <- paheDec sk c3
        let expectedSum = paheToPlaintext pk $ map (uncurry (+)) (zip ms1 ms2)
        unless (expectedSum `isPrefixOf` d1) $ error "Simd add is broken"

        putTextLn "Simd mul"
        c4 <- paheSIMDMulScal pk c1 scal
        putTextLn "Simd mul done"
        d2 <- paheDec sk c4
        let expectedProd = paheToPlaintext pk $ map (uncurry (*)) (zip ms1 scal)
        unless (expectedProd `isPrefixOf` d2) $ error "Simd mul is broken"

    putTextLn "OK"

testPaillier :: Int -> IO ()
testPaillier bits = do
    putTextLn $ "Testing Paillier, bits: " <> show bits
    let test = do
          (p,q,r,m1,m2) <- genDataPaillier bits
          let n = p * q
          let n2 = n * n

          let attempts = 300

          let bN = fromIntegral $ length $ inbase b64 n2

          p' <- toBignum bN p
          q' <- toBignum bN q
          n' <- toBignum bN n
          n2' <- toBignum bN n2
          g' <- toBignum bN (n + 1)
          r' <- toBignum bN r
          m1' <- toBignum bN m1
          m2' <- toBignum bN m2
          lambda' <- toBignum bN 0
          l2inv' <- toBignum bN 0

          paillierToSec bN p' q' n' n2' g' lambda' l2inv'

          c1 <- toBignum bN 0
          c2 <- toBignum bN 0
          c3 <- toBignum bN 0
          d <- toBignum bN 0

          time1 <- P.getPOSIXTime

          replicateM_ (attempts-1) $ paillierEnc bN n' n2' g' r' m1' c1
          paillierEnc bN n' n2' g' r' m2' c2

          time2 <- P.getPOSIXTime

          replicateM_ attempts $ paillierDec bN p' q' n' n2' g' lambda' l2inv' c1 d

          time3 <- P.getPOSIXTime

          replicateM_ attempts $ paillierHomAdd bN n' n2' c1 c2 c3

          time4 <- P.getPOSIXTime

          replicateM_ attempts $ paillierHomMulScal bN n' n2' c1 m2' c3

          time5 <- P.getPOSIXTime


          m'' <- fromBignum bN d
          when (m1 /= m'') $ error $ "Paillier failed: " <> show (p,q,r,m1)

          pure ( (time2 - time1) / fromIntegral attempts
               , (time3 - time2) / fromIntegral attempts
               , (time4 - time3) / fromIntegral attempts
               , (time5 - time4) / fromIntegral attempts)

    timings <- replicateM 1 test

    let average xs = foldr1 (+) xs / fromIntegral (length xs)
    let avg1 = average $ map (view _1) timings
    let avg2 = average $ map (view _2) timings
    let avg3 = average $ map (view _3) timings
    let avg4 = average $ map (view _4) timings

    putTextLn $ "Enc: " <> show (avg1 * 1000000) <> " mcs"
    putTextLn $ "Dec: " <> show (avg2 * 1000000) <> " mcs"
    putTextLn $ "Add: " <> show (avg3 * 1000000) <> " mcs"
    putTextLn $ "Mul: " <> show (avg4 * 1000000) <> " mcs"

testPaillierPahe :: IO ()
testPaillierPahe = do
    putTextLn "Testing paillier PAHE"

    let n = 5
    let l::Integer = 8
    sk <- paheKeyGen @PailSep n (2^l)
    let pk = paheToPublic sk

    ms1 <- replicateM n $ randomRIO (0, 2^l)
    ms2 <- replicateM n $ randomRIO (0, 2^l)

    c1 <- paheEnc pk ms1
    c2 <- paheEnc pk ms2
    c3 <- paheSIMDAdd pk c1 c2
    d <- paheDec sk c3

    print $ d == map (uncurry (+)) (zip ms1 ms2)



testDGK :: Int -> Integer -> Int -> IO ()
testDGK primeN primeBound bits = do
    putTextLn "Testing DGK"

    (uprimes,p,q,u,v,g,h) <- dgkKeyGenWithLookup primeN primeBound bits
    --(uprimes,p,q,u,v,g,h) <- dgkKeyGenWithLookup 1 3900 1024
    let ufact = map (,1) uprimes
    unless (L.exp (p*q) h v == 1) $ error "generated params are broken"
    unless (L.exp (p*q) g (u*v) == 1) $ error "generated params are broken"
    let n = p * q
    let bN = fromIntegral $ length $ inbase b64 n

    putTextLn "Params generated!"


    p' <- toBignum bN p
    q' <- toBignum bN q
    n' <- toBignum bN n
    u' <- toBignum bN u
    g' <- toBignum bN g
    h' <- toBignum bN h
    u_ps <- toBignumList bN primeN $ map fst ufact
    u_es <- toBignumList bN primeN $ map snd ufact
    v' <- toBignum bN v

    let test = do
          m1 <- randomRIO (0,u-1)
          m2 <- randomRIO (0,u-1)
          r <- randomRIO (0,n-1)

          let attempts = 20

          r' <- toBignum bN r
          m1' <- toBignum bN m1
          m2' <- toBignum bN m2

          c1 <- toBignum bN 0
          c2 <- toBignum bN 0
          c3 <- toBignum bN 0
          c4 <- toBignum bN 0
          d <- toBignum bN 0


          let decrypt ciph =
                  dgkDec bN (fromIntegral $ length ufact)
                    p' q' n' u' u_ps u_es v' g' h' ciph d

          time1 <- P.getPOSIXTime

          replicateM_ (attempts-1) $ dgkEnc bN n' u' g' h' r' m1' c1
          dgkEnc bN n' u' g' h' r' m2' c2

          time2 <- P.getPOSIXTime

          replicateM_ attempts $ decrypt c1

          time3 <- P.getPOSIXTime

          replicateM_ attempts $ dgkHomAdd bN n' c1 c2 c3

          time4 <- P.getPOSIXTime

          replicateM_ attempts $ dgkHomMulScal bN n' c1 m2' c4

          time5 <- P.getPOSIXTime

          c'' <- fromBignum bN c1
          unless (c'' == (L.exp n g m1 * L.exp n h r) `mod` n) $
              error "encryption is broken"

          m'' <- fromBignum bN d
          when (m1 /= m'') $ error $ "DGK failed: " <> show (p,q,r,m1, m'')

          decrypt c3
          m3 <- fromBignum bN d
          when (m3 /= (m1 + m2) `mod` u) $ error "DGK hom add failed"

          decrypt c4
          m4 <- fromBignum bN d
          when (m4 /= (m1 * m2) `mod` u) $ error "DGK hom mul failed"

          pure ( (time2 - time1) / fromIntegral attempts
               , (time3 - time2) / fromIntegral attempts
               , (time4 - time3) / fromIntegral attempts
               , (time5 - time4) / fromIntegral attempts
               )

    timings <- replicateM 1 test

    let average' xs = foldr1 (+) xs / fromIntegral (length xs)
    let avg1 = average' $ map (view _1) timings
    let avg2 = average' $ map (view _2) timings
    let avg3 = average' $ map (view _3) timings
    let avg4 = average' $ map (view _4) timings

    putTextLn $ "Enc: " <> show (avg1 * 1000000) <> " mcs"
    putTextLn $ "Dec: " <> show (avg2 * 1000000) <> " mcs"
    putTextLn $ "Add: " <> show (avg3 * 1000000) <> " mcs"
    putTextLn $ "Mul: " <> show (avg4 * 1000000) <> " mcs"

testDGKPahe :: IO ()
testDGKPahe = do
    putTextLn "Testing DGK PAHE"

    let dotest n = do
          putTextLn $ "Testing with n " <> show n
          let bound = (64 * 3 + 1)
          sk <- paheKeyGen @DgkCrt n bound
          let pk = paheToPublic sk
          putTextLn "Keygen done, running tests"
          let m = 1
          values1 <- replicateM m $ randomRIO (0, bound-1)
          values1' <- replicateM m $ randomRIO (0, bound-1)
          values2 <- replicateM n $ randomRIO (0, bound-1)
          values2' <- replicateM n $ randomRIO (0, bound-1)
          c1 <- paheEnc pk values1
          c1' <- paheEnc pk values1'
          c2 <- paheEnc pk values2
          c2' <- paheEnc pk values2'


          time1 <- P.getPOSIXTime

          replicateM_ 1000 $ void $ paheEnc pk values1

          time2 <- P.getPOSIXTime

          replicateM_ 1000 $ void $ paheEnc pk values2

          time3 <- P.getPOSIXTime

          replicateM_ 1000 $ void $ paheSIMDMulScal pk c1 values1

          time4 <- P.getPOSIXTime

          replicateM_ 1000 $ void $ paheSIMDMulScal pk c2 values2

          time5 <- P.getPOSIXTime

          replicateM_ 1000 $ void $ paheSIMDAdd pk c1 c1'

          time6 <- P.getPOSIXTime

          replicateM_ 1000 $ void $ paheSIMDAdd pk c2 c2'

          time7 <- P.getPOSIXTime

          replicateM_ 1000 $ void $ paheSIMDSub pk c1 c1'

          time8 <- P.getPOSIXTime

          replicateM_ 1000 $ void $ paheSIMDSub pk c2 c2'

          time9 <- P.getPOSIXTime


          putTextLn $ "Enc 1: " <> show ((time2-time1)) <> " ms"
          putTextLn $ "Enc 32: "<> show ((time3-time2)) <> " ms"
          putTextLn $ "Mul 1: " <> show ((time4-time3)) <> " ms"
          putTextLn $ "Mul 32: "<> show ((time5-time4)) <> " ms"
          putTextLn $ "Add 1: " <> show ((time6-time5)) <> " ms"
          putTextLn $ "Add 32: "<> show ((time7-time6)) <> " ms"
          putTextLn $ "Sub 1: " <> show ((time8-time7)) <> " ms"
          putTextLn $ "Sub 32: "<> show ((time9-time8)) <> " ms"

    dotest 1
--    dotest 8
--    dotest 16
    dotest 32

--instance (NFData a1, NFData a2, NFData a3, NFData a4, NFData a5,
--          NFData a6, NFData a7, NFData a8, NFData a9, NFData a10) =>
--         NFData (a1, a2, a3, a4, a5, a6, a7, a8, a9, a10) where
--    rnf (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) =
--        rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq`
--        rnf x6 `seq` rnf x7 `seq` rnf x8 `seq` rnf x9 `seq` rnf x10


testDGKPaheCriterion :: IO ()
testDGKPaheCriterion = defaultMain [
      env (genEnv 1) benches
    , env (genEnv 8) benches
    , env (genEnv 16) benches
    , env (genEnv 32) benches
    ]
  where
    genEnv n = do
      let bound = (64 * 3 + 1)
      sk <- paheKeyGen @DgkCrt n bound
      let pk = paheToPublic sk
      values1 <- replicateM 1 $ randomRIO (0, bound-1)
      values1' <- replicateM 1 $ randomRIO (0, bound-1)
      values2 <- replicateM n $ randomRIO (0, bound-1)
      values2' <- replicateM n $ randomRIO (0, bound-1)
      c1 <- paheEnc pk values1
      c1' <- paheEnc pk values1'
      c2 <- paheEnc pk values2
      c2' <- paheEnc pk values2'
      pure (n, sk, pk, values1, values2, c1, c1', c2, c2')

    benches ~(n, sk, pk, values1, values2, c1, c1', c2, c2') =
      bgroup ("n = " <> show n) $
      [ bench "Enc 1" $ whnfIO $ void $ paheEnc pk values1
      , bench "Add 1" $ whnfIO $ void $ paheSIMDAdd pk c1 c1'
      , bench "Mul 1" $ whnfIO $ void $ paheSIMDMulScal pk c1 values1
      , bench "Isz 1" $ whnfIO $ void $ paheIsZero sk c1
      ] ++ if n == 1 then [] else
      [ bench "Enc n" $ whnfIO $ void $ paheEnc pk values2
      , bench "Add n" $ whnfIO $ void $ paheSIMDAdd pk c2 c2'
      , bench "Mul n" $ whnfIO $ void $ paheSIMDMulScal pk c2 values2
      , bench "Isz n" $ whnfIO $ void $ paheIsZero sk c2
      ]
