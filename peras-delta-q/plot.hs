import Control.Exception (IOException, SomeException, try)
import Control.Monad
import Data.Functor (void)
import Data.Maybe (catMaybes)
import Data.Text
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as M
import System.IO
import Text.Read

main :: IO ()
main = do
  -- 1000 x 10ms buckets
  buckets <- M.replicate @_ @Int 1000 0
  withFile "blockperf_100000000-119353349.csv" ReadMode $ \h ->
    loop h buckets
  withFile "block-diffusion" WriteMode $ \h -> do
    total :: Double <- fromIntegral . V.sum <$> V.freeze buckets
    void $ M.ifoldM' (\acc i v -> hPutStrLn h (show i <> "\t" <> show (fromIntegral (v + acc) / total)) >> pure (v + acc)) 0 buckets
 where
  loop h buckets =
    try (hGetLine h) >>= \case
      Left (_ :: IOException) -> pure ()
      Right line -> do
        let delays = Prelude.drop 4 . split (== ',') . pack $ line
            delay = sum @_ @Int . catMaybes . fmap (fmap (`div` 10) . readMaybe . unpack) $ delays
        when (delay <= 1000 && delay > 0) $ M.modify buckets succ (delay - 1)
        loop h buckets
