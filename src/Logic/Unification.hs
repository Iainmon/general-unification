{-# LANGUAGE PatternSynonyms #-}

module Logic.Unification where

import qualified Data.Unification as U
import Control.Unification
import Data.List (intercalate)
import GHC.Generics -- (Generic(..))


data TreeF k a = TreeF k [a] deriving (Eq, Functor, Foldable, Traversable, Generic)

instance (Show k, Show a) => Show (TreeF k a) where
  show (TreeF k ts) = show k ++ " ⟨" ++ intercalate "," (map show ts) ++ "⟩"


type UTermInternal k v = U.UTerm (TreeF k) v


data UTerm k v
  = UVar v
  | UTerm k [UTerm k v]
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

pattern Lit :: k -> UTerm k v
pattern Lit x = UTerm x []


embed :: UTerm k v -> U.UTerm (TreeF k) v
embed (UVar v) = U.UVar v
embed (UTerm k ts) = U.UTerm (TreeF k (map embed ts))

pattern UUVar v = U.UVar v
pattern UUTerm k ts = U.UTerm (TreeF k ts)

unembed :: UTermInternal k v -> UTerm k v
unembed (UUVar v) = UVar v
unembed (UUTerm k ts) = UTerm k (map unembed ts)


class (Ord v, Show v) => Variable v where
  toInt :: v -> Int


-- class UnificationTerm t where
--   embed :: t k v -> Term k v


-- zipMatch :: t a -> t a -> Maybe (t (Either a (a,a)))

-- instance Eq k => Unifiable (TreeF k) where
--   zipMatch :: TreeF k a -> TreeF k a -> Maybe (TreeF k (Either a (a,a)))
--   zipMatch (TreeF k ts) (TreeF k' ts') | k == k'
--     = Just $ TreeF k (zipWith (\t t' -> Right (t,t')) ts ts')

  -- zipMatch (TreeF k ts) (TreeF k' ts') | k == k' 
  --   = TreeF (Left k) (zipWith (\t t' -> Right (t,t')) ts ts')