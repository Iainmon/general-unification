

sequence :: Monad m => [m a] -> m [a]
sequence [] = return []
-- sequence (m:ms) = m >>= \x -> sequence ms >>= \xs -> return (x:xs)
sequence (m:ms) = do
  x <- m
  xs <- sequence ms
  return (x:xs)

mapM :: Monad m => (a -> m b) -> [a] -> m [b]

traverse :: Applicative f => (a -> f b) -> [a] -> f [b]
traverse :: (a -> [] b) -> [a] -> [] [b]
traverse f = sequence . map f