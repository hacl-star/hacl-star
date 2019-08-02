module TestHacl where

import Universum

import qualified Foreign.Marshal as A

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

createBignum :: Integer -> IO Bignum
createBignum x =
    let els = map fromInteger $ inbase b64 x in
    A.newArray els

fromBignum :: Int -> Bignum -> IO Integer
fromBignum n x = do
    els <- A.peekArray n x
    print els
    pure $ frombase b64 $ map toInteger els


testHacl :: IO ()
testHacl = do
    a <- createBignum 500
    print =<< fromBignum 1 a
    b <- createBignum 100
    print =<< fromBignum 1 b

    c <- createBignum 0
    bnSub 1 1 a b c
    print =<< fromBignum 1 c

    d <- createBignum 0
    bnMulFitting 1 1 1 a b d
    print =<< fromBignum 1 d

    putText "mda\n"

testPaillier :: IO ()
testPaillier = do
    (p,q,r,m) <- genDataPaillier 30
    let n = p * q
    let n2 = n * n
    when (n2 >= b64) $ error "hz bratan"

data PaillierSec =
    PaillierSec
        { ps_p      :: !Bignum
        , ps_q      :: !Bignum
        , ps_n      :: !Bignum
        , ps_n2     :: !Bignum
        , ps_g      :: !Bignum
        , ps_lambda :: !Bignum
        , ps_l2inv  :: !Bignum
        }



    putTextLn "mda"
