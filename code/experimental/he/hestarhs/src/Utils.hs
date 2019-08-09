-- | General-purpose utility functions.

module Utils where

import Universum

import Control.Concurrent (withMVar)
import qualified Data.Time.Clock.POSIX as P
import System.IO.Unsafe (unsafePerformIO)

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


findM :: Monad m => (a -> m Bool) -> [a] -> m (Maybe a)
findM _ []     = return Nothing
findM p (x:xs) = ifM (p x) (return $ Just x) (findM p xs)

measureTimeSingle :: Text -> IO a -> IO a
measureTimeSingle label action = do
    time0 <- P.getPOSIXTime
    r <- action
    time1 <- P.getPOSIXTime
    logRaw $ label <> " took : " <> show (round ((time1-time0) * 1000) :: Integer) <> "ms"
    pure r

simdadd :: Num a => [a] -> [a] -> [a]
simdadd x y = map (uncurry (+)) (zip x y)

simdmul :: Num a => [a] -> [a] -> [a]
simdmul x y = map (uncurry (*)) (zip x y)

dotprod :: [Integer] -> [Integer] -> Integer
dotprod x y = sum $ simdmul x y
