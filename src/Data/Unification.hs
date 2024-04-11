{-# LANGUAGE UndecidableInstances #-}
module Data.Unification where

data UTerm t v
  = UVar v
  | UTerm (t (UTerm t v))


instance (Show (t (UTerm t v)), Show v) => Show (UTerm t v) where
  showsPrec p (UVar v) = showsPrec p v
  showsPrec p (UTerm t) = showsPrec p t

instance (Eq (t (UTerm t v)), Eq v) => Eq (UTerm t v) where
  UVar v == UVar v' = v == v'
  UTerm t == UTerm t' = t == t'
  _ == _ = False

instance Functor t => Functor (UTerm t) where
  fmap :: (a -> b) -> UTerm t a -> UTerm t b
  fmap f (UVar v)  = UVar $ f v
  fmap f (UTerm t) = UTerm $ fmap (fmap f) t

instance Foldable t => Foldable (UTerm t) where
  foldMap :: Monoid m => (v -> m) -> UTerm t v -> m
  foldMap f (UVar v)  = f v
  foldMap f (UTerm t) = foldMap (foldMap f) t

instance Traversable t => Traversable (UTerm t) where
  traverse :: Applicative f => (a -> f b) -> UTerm t a -> f (UTerm t b)
  traverse f (UVar v)  = UVar <$> f v
  traverse f (UTerm t) = UTerm <$> traverse (traverse f) t

instance Functor t => Applicative (UTerm t) where
  pure :: a -> UTerm t a
  pure = UVar

  (<*>) :: UTerm t (a -> b) -> UTerm t a -> UTerm t b
  UVar f <*> UVar x  = UVar $ f x
  UVar f <*> UTerm t = UTerm $ fmap f <$> t
  UTerm t <*> x      = UTerm $ (<*> x) <$> t

instance Functor t => Monad (UTerm t) where
  (>>=) :: UTerm t a -> (a -> UTerm t b) -> UTerm t b
  UVar x >>= f  = f x
  UTerm t >>= f = UTerm $ (>>= f) <$> t


data UFailure t v
  = Occurs v (UTerm t v)
  | Mismatch (t (UTerm t v)) (t (UTerm t v))

instance (Show (t (UTerm t v)), Show v) => Show (UFailure t v) where
  showsPrec p (Occurs v t) = showParen (p > 9) (showString "Occurs " . showsPrec 11 v . showString " " . showsPrec 11 t)
  showsPrec p (Mismatch t t') = showParen (p > 9) (showString "Mismatch " . showsPrec 11 t . showString " " . showsPrec 11 t')