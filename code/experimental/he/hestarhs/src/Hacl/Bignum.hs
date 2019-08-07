-- | Some functions to work with bignums.

module Hacl.Bignum where

import Universum

import qualified Data.ByteString as BS
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

toBignumExact :: Integer -> IO (Bignum, Word32)
toBignumExact x = do
    let vals = map fromInteger $ inbase b64 x
    bn <- A.newArray vals
    pure (bn, fromIntegral $ length vals)

toBignumList :: Word32 -> [Integer] -> IO BignumList
toBignumList l xs = A.newArray $ concatMap (toBignumRaw l) xs

toBignumBS :: Word32 -> ByteString -> IO Bignum
toBignumBS n s = toBignum n $ conv $ BS.unpack s
  where
    conv :: [Word8] -> Integer
    conv = frombase 256 . map fromIntegral

fromBignumRaw :: Word32 -> Bignum -> IO [Word64]
fromBignumRaw n x = A.peekArray (fromIntegral n) x

fromBignumBS :: Word32 -> Bignum -> IO ByteString
fromBignumBS n x = BS.pack . concatMap (pad . split) <$> fromBignumRaw n x
  where
    pad :: [Word8] -> [Word8]
    pad y = y ++ replicate (8 - length y) 0
    split :: Word64 -> [Word8]
    split = map fromIntegral . inbase 256 . fromIntegral

fromBignum :: Word32 -> Bignum -> IO Integer
fromBignum n x = fmap (frombase b64 . map toInteger) $ fromBignumRaw n x

freeBignum :: Bignum -> IO ()
freeBignum = A.free
