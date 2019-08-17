-- | General-purpose utility functions.

module Utils where

import Universum

import Control.Concurrent (withMVar)
import qualified Data.Array.IO as AIO
import qualified Data.ByteString as BS
import qualified Data.Time.Clock.POSIX as P
import System.IO.Unsafe (unsafePerformIO)
import System.Random (randomRIO)

getCurrentTimeMcs :: IO Integer
getCurrentTimeMcs = floor . (*1000000) <$> P.getPOSIXTime

getCurrentTimeMs :: IO Integer
getCurrentTimeMs = floor . (*1000) <$> P.getPOSIXTime

lMVar :: MVar ()
lMVar = unsafePerformIO $ newMVar ()

logRaw :: MonadIO m => Text -> m ()
logRaw x = do
    t <- liftIO getCurrentTimeMs
    liftIO $ withMVar lMVar $ \() ->
      putTextLn (show (t`div`1000) <> "." <> show (t`mod`1000) <> " " <> x) >> pure ()

log :: MonadIO m => Text -> m ()
log x = if False then pass else logRaw x

lambda :: Integral a => a
lambda = 80

average :: Integral a => [a] -> a
average xs = foldr1 (+) xs `div` fromIntegral (length xs)

findM :: Monad m => (a -> m Bool) -> [a] -> m (Maybe a)
findM _ []     = return Nothing
findM p (x:xs) = ifM (p x) (return $ Just x) (findM p xs)

measureTimeRet :: IO a -> IO (a,Integer)
measureTimeRet action = do
    time0 <- getCurrentTimeMcs
    r <- action
    time1 <- getCurrentTimeMcs
    let delta = time1-time0
    pure (r, delta)

measureTimeSingle :: Text -> IO a -> IO a
measureTimeSingle label action = do
    (a,delta) <- measureTimeRet action
    logRaw $ label <> " took : " <> show delta <> "mcs"
    pure a

simdadd :: Num a => [a] -> [a] -> [a]
simdadd x y = map (uncurry (+)) (zip x y)

simdmul :: Num a => [a] -> [a] -> [a]
simdmul x y = map (uncurry (*)) (zip x y)

dotprod :: [Integer] -> [Integer] -> Integer
dotprod x y = sum $ simdmul x y

-- taken from https://wiki.haskell.org/Random_shuffle
shuffle :: [a] -> IO [a]
shuffle xs = do
        ar <- newArray' n xs
        forM [1..n] $ \i -> do
            j <- randomRIO (i,n)
            vi <- AIO.readArray ar i
            vj <- AIO.readArray ar j
            AIO.writeArray ar j vi
            return vj
  where
    n = length xs
    newArray' :: Int -> [a] -> IO (AIO.IOArray Int a)
    newArray' n' xs' =  AIO.newListArray (1,n') xs'
