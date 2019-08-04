-- | Some functions to work with bignums.

module Hacl.Bignum where

import Universum

import qualified Foreign.Marshal as A

import Hacl.Raw

inbase :: Integer -> Integer -> [Integer]
inbase base i = i `mod` base : (case (i `div` base) of
                                  0  -> []
                                  i' -> inbase base i')

frombase :: Integer -> [Integer] -> Integer
frombase base is = sum $ map (\(i,a) -> a * (base^i)) $ zip [(0::Integer)..] is

b64 :: Integer
b64 = 2^(64::Integer)

toBignumRaw :: Word32 -> Integer -> [Word64]
toBignumRaw l x =
    let els = map fromInteger $ inbase b64 x in
    if fromIntegral l < length els
      then error "toBignum: length requested is too small"
      else els ++ replicate (fromIntegral l - length els) 0

toBignum :: Word32 -> Integer -> IO Bignum
toBignum l x = A.newArray $ toBignumRaw l x

toBignumExact :: Integer -> IO Bignum
toBignumExact x = A.newArray $ map fromInteger $ inbase b64 x

toBignumList :: Word32 -> [Integer] -> IO BignumList
toBignumList l xs = A.newArray $ concatMap (toBignumRaw l) xs


fromBignum :: Word32 -> Bignum -> IO Integer
fromBignum n x = do
    els <- A.peekArray (fromIntegral n) x
    pure $ frombase b64 $ map toInteger els
