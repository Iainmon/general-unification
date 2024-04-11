{-# LANGUAGE FunctionalDependencies, DefaultSignatures #-}

module Control.Unification where

import Data.Unification
import GHC.Generics

class Traversable t => Unifiable t where
  zipMatch :: t a -> t a -> Maybe (t (Either a (a,a)))
  default zipMatch :: (Generic1 t, Unifiable (Rep1 t)) => t a -> t a -> Maybe (t (Either a (a, a)))
  zipMatch a b = to1 <$> zipMatch (from1 a) (from1 b)
  -- unify :: Eq v => UTerm t v -> UTerm t v -> Maybe (UTerm t v)


class (Unifiable t, Monad m) => BindingMonad t v m | m t -> v, v m -> t where
  bind :: v -> UTerm t v -> m ()
  lookupVar :: v -> m (UTerm t v)

instance Unifiable V1 where
    zipMatch a _ = Just $ Left <$> a

instance Unifiable U1 where
    zipMatch a _ = Just $ Left <$> a

instance Unifiable Par1 where
    zipMatch (Par1 a) (Par1 b) = Just . Par1 $ Right (a,b)

instance Unifiable f => Unifiable (Rec1 f) where
    zipMatch (Rec1 a) (Rec1 b) = Rec1 <$> zipMatch a b

instance Eq c => Unifiable (K1 i c) where
    zipMatch (K1 a) (K1 b)
        | a == b    = Just (K1 a)
        | otherwise = Nothing

instance Unifiable f => Unifiable (M1 i c f) where
    zipMatch (M1 a) (M1 b) = M1 <$> zipMatch a b

instance (Unifiable f, Unifiable g) => Unifiable (f :+: g) where
    zipMatch (L1 a) (L1 b) = L1 <$> zipMatch a b
    zipMatch (R1 a) (R1 b) = R1 <$> zipMatch a b
    zipMatch _ _ = Nothing

instance (Unifiable f, Unifiable g) => Unifiable (f :*: g) where
    zipMatch (a1 :*: a2) (b1 :*: b2) =
        (:*:) <$> zipMatch a1 b1 <*> zipMatch a2 b2

instance (Unifiable f, Unifiable g) => Unifiable (f :.: g) where
    zipMatch (Comp1 fga) (Comp1 fgb) =
        Comp1 <$> (traverse step =<< zipMatch fga fgb)
        where
        -- TODO: can we avoid mapping 'Left' all the way down?
        step (Left  gx)       = Just (Left <$> gx)
        step (Right (ga, gb)) = zipMatch ga gb