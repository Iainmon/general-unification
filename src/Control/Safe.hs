module Control.Safe where

import System.IO.Unsafe (unsafePerformIO)
import qualified Control.Exception as Exc

{-# NOINLINE safe #-}
safe :: a -> Maybe a
safe x = unsafePerformIO $ Exc.catch (x `seq` return (Just x)) handler
    where
    handler exc = return Nothing  `const`  (exc :: Exc.ErrorCall)
