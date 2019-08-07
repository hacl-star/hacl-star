-- | Methods to support PAHE, like key generation, packing modes, etc.

module Hacl.Support where

import Universum hiding (exp, last, (<*>))

import Data.List (splitAt)
import Numeric (log)
import System.IO.Unsafe (unsafePerformIO)
import System.Random (randomIO, randomRIO)

import Hacl.Bignum
import Hacl.Raw
import Lib hiding (crt)
import Utils

testPrime :: Integer -> Bool
testPrime i = unsafePerformIO $ do
    (p,sz) <- toBignumExact i
    r <- bnIsPrime sz p
    freeBignum p
    pure r

-- https://stackoverflow.com/questions/6325576/how-many-iterations-of-rabin-miller-should-i-use-for-cryptographic-safe-primes
genPrime :: Int -> IO Integer
genPrime bits = do
    p <- randomRIO (2 ^ (bits - 4),2 ^ bits) `suchThat` odd
    if testPrime p
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


log2 :: Integer -> Integer
log2 x = ceiling $ log (fromIntegral (x+1)) / log 2

fromFacts :: [(Integer,Integer)] -> Integer
fromFacts = product . map (\(p,i) -> p ^ i)

recombineFacts :: [(Integer,Integer)] -> [(Integer,Integer)]
recombineFacts xs =
    let ps = ordNub $ map fst xs in
    map (\p -> (p,sum $ map snd $ filter ((== p). fst) xs)) ps

flattenFacts :: [(Integer,Integer)] -> [Integer]
flattenFacts = concatMap (\(p,j) -> replicate (fromIntegral j) p)

factToOrders :: [(Integer,Integer)] -> [Integer]
factToOrders facts  =
    sort $ ordNub $ map product $ allCombinations $ flattenFacts facts

orderFact :: [Integer] -> Integer -> Integer -> Integer
orderFact possibleOrders n g =
    fromMaybe (error "can't be") $ find (\o -> exp n g o == 1) $ sort possibleOrders

fastFindOrder :: Integer -> Integer -> [Integer] -> IO Integer
fastFindOrder n g flatFactors = do

    let checkProduct :: [Integer] -> IO Bool
        checkProduct listPrimes = pure $ exp n g (product listPrimes) == 1

    let loop extraPrms = do
            if extraPrms == [] then pure []
            else do
                resIndex <-
                    findM (\i -> checkProduct (listRem extraPrms i))
                          [0..length extraPrms-1]
                case resIndex of
                    Nothing -> pure extraPrms
                    Just i  -> loop (listRem extraPrms i)

    product <$> loop flatFactors
  where
    listRem ls i = let (ls1,ls2) = splitAt i ls in ls1 ++ drop 1 ls2

findWithOrder :: Integer -> Integer -> Integer -> [Integer] -> Integer -> IO Integer
findWithOrder p q n (sort -> posOrders) reqO = do
    let bn = fromIntegral $ log2 n

    bnZero <- toBignum bn 0
    bnOne <- toBignum bn 1
    p' <- toBignum bn p
    q' <- toBignum bn q
    n' <- toBignum bn n
    reqO' <- toBignum bn reqO
    posOrders' <- mapM (toBignum bn) posOrders

    -- openssl version must be faster
    let randomBignum = toBignum bn =<< randomRIO (0,n-1)

    e <- toBignum bn 0
    let orderFactBN :: Bignum -> Bignum -> IO Bignum
        orderFactBN modulo g =
            fromMaybe (error "can't be") <$>
            findM (\o -> do
                        bnModExp bn bn modulo g o e
                        bnIsEqual bn bn e bnOne)
            posOrders'


    rem1 <- toBignum bn 0
    oDivReqo <- toBignum bn 0
    oModReqo <- toBignum bn 0 -- not used
    cand <- toBignum bn 0
    candModP <- toBignum bn 0
    candModQ <- toBignum bn 0
    let go i = do
            g <- randomBignum
            o <- orderFactBN n' g
            bnRemainder bn bn o reqO' rem1
            cond1 <- bnIsEqual bn bn rem1 bnZero
            if cond1 then do
                bnDivide bn o reqO' oDivReqo oModReqo
                bnModExp bn bn n' g oDivReqo cand -- cand = g^(
                bnRemainder bn bn cand p' candModP
                bnRemainder bn bn cand q' candModQ
                o1 <- orderFactBN p' candModP
                o2 <- orderFactBN q' candModQ

                b1 <- bnIsEqual bn bn o1 o2
                b2 <- bnIsEqual bn bn o1 reqO'
                if b1 && b2 then pure cand
                else go (i+1)
            else go (i+1)

    fromBignum bn =<< go 0

genDataDGK ::
       [(Integer, Integer)]
    -> Int
    -> IO (Integer, Integer, Integer, Integer, Integer, Integer)
genDataDGK uFacts bits = do
    let u = fromFacts uFacts
    let vbits = 160
    let ubits = fromIntegral $ log2 u
    let rbits = bits `div` 2 - ubits - vbits
    when (rbits < 0) $ error $ "genDataDGK: incorrect params: " <> show (vbits, ubits, rbits)

    v <- genPrime vbits
    let genR (i::Integer) = do
          r <- genPrime rbits
          let p = 2 * u * v * r + 1
          if testPrime p then pure (r,p) else genR (i+1)

    putTextLn "Generating p"
    (r_p,p) <- genR 0
    putTextLn "Generating q"
    (r_q,q) <- genR 0
    when (p == q) $ error "p = q"
    let n = p * q
    putTextLn "Generated n"

    let phinFacts =
            recombineFacts $
            [(2,2),(r_p,1),(r_q,1),(v,2)] <> uFacts <> uFacts
    unless (fromFacts phinFacts == (p-1)*(q-1)) $ error "er2"
    let flatFacts = flattenFacts phinFacts

    let findWithOrd reqO = do
            g <- randomRIO (0, (p-1)*(q-1))
            o <- fastFindOrder n g flatFacts
            if o `mod` reqO == 0 then do
                let cand = exp n g (o `div` reqO)
                o1 <- fastFindOrder p (cand `mod` p) flatFacts
                o2 <- fastFindOrder q (cand `mod` q) flatFacts
                if o1 == o2 && o1 == reqO then pure cand
                else findWithOrd reqO
            else findWithOrd reqO

    putTextLn "Generating g"
    g <- findWithOrd (u * v)
    putTextLn "Generating h"
    h <- findWithOrd v

    pure (p,q,u,v,g,h)

genConsecutivePrms :: Int -> Integer -> [Integer]
genConsecutivePrms n bound =
    reverse $ go 0 [] (if even bound then bound+1 else bound+2)
  where
    go l xs toTest = if l >= n then xs else
        if testPrime toTest
        then go (l+1) (toTest:xs) (toTest+2)
        else go l xs (toTest+2)

genDataDGKWithPrimes ::
       Int
    -> Integer
    -> Int
    -> IO ([Integer], Integer, Integer, Integer, Integer, Integer, Integer)
genDataDGKWithPrimes primeN primeBound bits = do
    let prms = genConsecutivePrms primeN primeBound
    let ulog = sum $ map log2 prms
    (p,q,u,v,g,h) <- genDataDGK (map (,1) prms) bits
    pure (prms,p,q,u,v,g,h)
