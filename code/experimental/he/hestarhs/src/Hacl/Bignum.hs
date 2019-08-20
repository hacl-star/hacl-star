-- | Some functions to work with bignums.

module Hacl.Bignum where

import Universum

import Data.Bits (shiftR, (.&.))
import qualified Data.ByteString as BS
import qualified Foreign.Marshal as A
import Foreign.Ptr (castPtr)

import Hacl.Raw

{-# INLINE b64 #-}
b64 :: Integer
b64 = 0x10000000000000000

inbase :: Integer -> Integer -> [Integer]
inbase base i | i < base = [i]
inbase base i = i `mod` base : inbase base (i `div` base)

inbase64 :: Integer -> [Word64]
inbase64 i | i < b64 = [fromInteger i]
inbase64 i = fromIntegral (i .&. 0xffffffffffffffff) : inbase64 (shiftR i 64)

frombase :: Integer -> [Integer] -> Integer
frombase base is = sum $ map (\(i,a) -> a * (base^i)) $ zip [(0::Integer)..] is

toBignumRaw :: Word32 -> Integer -> [Word64]
toBignumRaw l x =
    let els = inbase64 x in
    if fromIntegral l < length els
      then error "toBignum: length requested is too small"
      else els ++ replicate (fromIntegral l - length els) 0

toBignumZero :: Word32 -> IO Bignum
toBignumZero = A.callocArray . fromIntegral

toBignumZeroTest :: IO ()
toBignumZeroTest = do
    bn <- toBignumZero 5
    print =<< fromBignum 5 bn

toBignum :: Word32 -> Integer -> IO Bignum
toBignum l x = do
    b <- A.callocArray (fromIntegral l)
    A.pokeArray b (inbase64 x)
    pure b
    --A.newArray $ toBignumRaw l x

toBignumExact :: Integer -> IO (Bignum, Word32)
toBignumExact x = do
    let vals = inbase64 x
    bn <- A.newArray vals
    pure (bn, fromIntegral $ length vals)

toBignumList :: Word32 -> Int -> [Integer] -> IO BignumList
toBignumList bn l xs = do
    --when (length xs > l) $ error "toBignumList bound"
    --(b :: Ptr Word64) <- A.callocArray (fromIntegral bn * l)
    --forM_ (xs `zip` [0..]) $ \(x,(i::Int)) ->
    --  A.pokeArray (plusPtr b (i * fromIntegral bn) :: Ptr Word64)
    --              (map fromInteger (inbase b64 x))
    --pure b
    A.newArray $ concatMap (toBignumRaw bn) (xs ++ replicate (l - length xs) 0)

toBignumBS :: Word32 -> ByteString -> IO Bignum
toBignumBS n s =
    castPtr <$>
    A.newArray (BS.unpack s ++ replicate ((fromIntegral n) * 8 - BS.length s) 0)


fromBignumRaw :: Word32 -> Bignum -> IO [Word64]
fromBignumRaw n x = A.peekArray (fromIntegral n) x

--fromBignumBS :: Word32 -> Bignum -> IO ByteString
--fromBignumBS n x = BS.pack . concatMap (pad . split) <$> fromBignumRaw n x
--  where
--    pad :: [Word8] -> [Word8]
--    pad y = y ++ replicate (8 - length y) 0
--    split :: Word64 -> [Word8]
--    split = map fromIntegral . inbase 256 . fromIntegral

fromBignumBS :: Word32 -> Bignum -> IO ByteString
fromBignumBS n x = BS.pack <$> A.peekArray (fromIntegral n * 8) (castPtr x)

fromBignum :: Word32 -> Bignum -> IO Integer
fromBignum n x = fmap (frombase b64 . map toInteger) $ fromBignumRaw n x

freeBignum :: Bignum -> IO ()
freeBignum = A.free

copyBignum :: Word32 -> Bignum -> IO Bignum
copyBignum n b = do
    ret <- toBignumZero n
    A.copyArray ret b (fromIntegral n)
    pure ret
