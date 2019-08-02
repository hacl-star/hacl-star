module TestHacl where

import Universum

import qualified Foreign.Marshal as A

import Hacl


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
    b <- createBignum 100
    c <- createBignum 0
    bn_sub 2 2 a b c
    res <- fromBignum 2 c
    print res
    putText "mda\n"
