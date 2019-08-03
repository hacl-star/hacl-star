module TestHacl where

import Universum

import qualified Data.Time.Clock.POSIX as P
import qualified Foreign.Marshal as A
import System.Random (randomIO)

import Hacl
import Playground

inbase :: Integer -> Integer -> [Integer]
inbase base i = i `mod` base : (case (i `div` base) of
                                  0  -> []
                                  i' -> inbase base i')

frombase :: Integer -> [Integer] -> Integer
frombase base is = sum $ map (\(i,a) -> a * (base^i)) $ zip [(0::Integer)..] is

b64 :: Integer
b64 = 2^(64::Integer)

toBignum :: Word32 -> Integer -> IO Bignum
toBignum l x =
    let els = map fromInteger $ inbase b64 x in
    if fromIntegral l < length els
      then error "toBignum: length requested is too small"
      else A.newArray $ els ++ replicate (fromIntegral l - length els) 0

toBignumExact :: Integer -> IO Bignum
toBignumExact x =
    let els = map fromInteger $ inbase b64 x in
    A.newArray els

fromBignum :: Word32 -> Bignum -> IO Integer
fromBignum n x = do
    els <- A.peekArray (fromIntegral n) x
    pure $ frombase b64 $ map toInteger els


testHacl :: IO ()
testHacl = do
    a <- toBignumExact 500
    print =<< fromBignum 1 a
    b <- toBignumExact 100
    print =<< fromBignum 1 b

    c <- toBignumExact 0
    bnSub 1 1 a b c
    print =<< fromBignum 1 c

    d <- toBignumExact 0
    bnMulFitting 1 1 1 a b d
    print =<< fromBignum 1 d

    putText "mda\n"


testGM :: Int -> IO ()
testGM bits = do
    putTextLn "Testing GM"
    let test = do
          (p,q,y,r,m1,m2) <- genDataGM bits
          let n = p * q

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


          time1 <- P.getPOSIXTime

          replicateM 99 $ gmEnc bN n' y' r' m1 c1
          gmEnc bN n' y' r' m2 c2

          time2 <- P.getPOSIXTime

          replicateM 99 $ gmDec bN p' pmin1 pmin1half c1
          m1' <- gmDec bN p' pmin1 pmin1half c1

          time3 <- P.getPOSIXTime

          replicateM 100 $ gmXor bN n' c1 c2 c3

          time4 <- P.getPOSIXTime


          when (m1 /= m1') $ error $ "GM failed: " <> show (p,q,y,r,m1,m2)
          pure (time2 - time1, time3 - time2, time4 - time3)

    let n = 10

    timings <- replicateM n test

    let average xs = foldr1 (+) xs / fromIntegral n
    let avg1 = average $ map (view _1) timings
    let avg2 = average $ map (view _2) timings
    let avg3 = average $ map (view _3) timings

    putTextLn $ "Enc: " <> show (avg1 * 100) <> " ms"
    putTextLn $ "Dec: " <> show (avg2 * 100) <> " ms"
    putTextLn $ "Xor: " <> show (avg3 * 100) <> " ms"


testPaillier :: Int -> IO ()
testPaillier bits = do
    putTextLn "Testing paillier"
    let test = do
          (p,q,r,m1,m2) <- genDataPaillier bits
          let n = p * q
          let n2 = n * n

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

          replicateM 100 $ paillierEnc bN n' n2' g' r' m1' c1

          time2 <- P.getPOSIXTime

          replicateM 100 $ paillierDec bN p' q' n' n2' g' lambda' l2inv' c1 d

          time3 <- P.getPOSIXTime

          replicateM 100 $ paillierHomAdd bN n' n2' c1 c2 c3

          time4 <- P.getPOSIXTime

          replicateM 100 $ paillierHomMulScal bN n' n2' c1 m2' c3

          time5 <- P.getPOSIXTime


          m'' <- fromBignum bN d
          when (m1 /= m'') $ error $ "Paillier failed: " <> show (p,q,r,m1)

          pure (time2 - time1, time3 - time2, time4 - time3, time5 - time4)

    let n = 100

    timings <- replicateM n test

    let average xs = foldr1 (+) xs / fromIntegral n
    let avg1 = average $ map (view _1) timings
    let avg2 = average $ map (view _2) timings
    let avg3 = average $ map (view _3) timings
    let avg4 = average $ map (view _4) timings

    putTextLn $ "Enc: " <> show (avg1 * 100) <> " ms"
    putTextLn $ "Dec: " <> show (avg2 * 100) <> " ms"
    putTextLn $ "Hom_add: " <> show (avg3 * 100) <> " ms"
    putTextLn $ "Hom_mul_scal: " <> show (avg4 * 100) <> " ms"

testDGK :: IO ()
testDGK = putTextLn "Testing DGK TODO"
