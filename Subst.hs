{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}


module Subst where

import ErrMaybe

import qualified Data.Map as Map
import Data.Map (Map)

import Data.List (intercalate)
import Data.Maybe (listToMaybe,isJust,fromJust)

type Name = String

data Term
  = Var Name
  | Term Name [Term]
  deriving (Eq, Ord)

lit :: Name -> Term
lit x = Term x []

occurs :: Name -> Term -> Bool
occurs x (Var y) = x == y
occurs x (Term _ ts) = any (occurs x) ts

subst :: Name -> Term -> (Term -> Term)
(x `subst` s) (Var y) | x == y    = s
                      | otherwise = Var y
(x `subst` s) (Term f ts)         = Term f (map (x `subst` s) ts)


class Substitution s where
  {-# MINIMAL empty, mapsTo, apply, compose #-}
  empty :: s
  mapsTo :: Name -> Term -> s
  apply :: s -> Term -> Term
  -- (<.) = flip apply
  compose :: s -> s -> s
  -- (<.>) = compose
  -- (t <. tau) <. sgm = t <. (sgm <.> tau)

(<.) :: Substitution s => Term -> s -> Term
(<.) = flip apply

(<.>) :: Substitution s => s -> s -> s
(<.>) = compose

ammend :: Substitution s => s -> Name -> Term -> s
ammend σ x t = σ <.> mapsTo x t

fromList :: Substitution s => [(Name, Term)] -> s
fromList = foldr (compose . uncurry mapsTo) empty

unifyOne :: forall s. Substitution s => Term -> Term -> s
unifyOne (Var x) t | not (x `occurs` t) = mapsTo x t
unifyOne t@(Term _ _) (Var x) | not (x `occurs` t) = mapsTo x t -- Not in the original (Mar 2)
unifyOne (Term f ts) (Term g ss) | f == g = unifyMany (zip ts ss)
unifyOne t s | t == s = empty
unifyOne (Var x) t | x `occurs` t = error "unifyOne: circularity"
unifyOne t (Var x) | x `occurs` t = error "unifyOne: circularity"
unifyOne _ _ = error "unifyOne: no unifier"

unifyMany :: forall s. Substitution s => [(Term, Term)] -> s
unifyMany [] = empty
unifyMany ((t,s):ts) = σ1 <.> σ2
  where σ2 = unifyMany ts
        σ1 = unifyOne (apply σ2 t) (apply σ2 s)
        bimap f (x,y) = (f x, f y)

-- t1 = Term "f" [Var "x", Var "a", Var "a"]
-- t2 = Term "f" [Var "b", Var "y", Var "x"]
-- works!
{-
ms = [("a", Var "b")]
m  = [("x",Var "a")]
emp = empty :: ListSubst
t = Term "f" [Var "x", Var "a"]
-- should: 
-- (t <. m) <. ms == t <. (ms <.> m) == f(b,b)
-- (ms <.> m) == [("a",b),("x",a)]
-- (t <. (ammend ms "x" (Var "a"))) == f(b,b)
-- [("a",b),("x",a)] == ammend (ammend [] "a" (Var "b")) "x" (Var "a")
-}

type ListSubst = [(Name, Term)]

instance Substitution ListSubst where
  empty = []
  mapsTo x t = [(x, t)]
  apply [] t          = t
  apply ((x, t'):σ) t = (x `subst` t') (apply σ t)
  compose = (++)


-- ms = mapsTo "a" (Var "b") :: MapSubst
-- m  = mapsTo "x" (Var "a") :: MapSubst
-- t = Term "f" [Var "x", Var "a"]

type MapSubst = Map Name Term

instance Substitution MapSubst where
  empty = Map.empty
  mapsTo = Map.singleton
  apply σ (Term f ts) = Term f (map (apply σ) ts)
  apply σ (Var x) | Just t <- Map.lookup x σ = t
                  | otherwise                = Var x
  compose σ τ = (Map.map (apply σ) τ) `Map.union` (σ \\ τ)
    where (\\) = Map.difference


instance Substitution (Name -> Maybe Term) where
  empty = \_ -> Nothing
  mapsTo x t = \y -> if x == y then Just t else Nothing
  apply σ (Var x) | Just t' <- σ x = t'
  apply _ t = t
  compose σ τ = \x -> case σ x of
    Just t -> Just t
    Nothing -> τ x


instance Show Term where
  show (Var x) = "\x1b[1m" ++ x ++ "\x1b[22m"
  show (Term f []) = "\x1b[4m" ++ f ++ "\x1b[24m"
  show (Term f ts) = "\x1b[3m" ++ f ++ "\x1b[23m" ++ "(" ++ intercalate "," (map show ts) ++ ")"


data Rule = R Name Term [Term]

data Proof s = Proof Name Term s [Proof s]

type Rules = [Rule]

deriveOne :: Substitution s => Term -> Rules -> Maybe (Proof s)
deriveOne t [] = Nothing
deriveOne t rs = firstJust (map proof rs)
  where proof (R rn pi ts) = do
          x <- return $ trace $ "deriveMany: " ++ show t
          sgm <- uc $ unifyOne t pi
          ps <- deriveMany (map (apply sgm) ts) rs
          Just $ Proof rn pi sgm ps
        firstJust [] = Nothing
        firstJust (Just x:_) = Just x
        firstJust (_:xs) = firstJust xs

deriveMany :: Substitution s => [Term] -> Rules -> Maybe [Proof s]
deriveMany [] _ = return []
deriveMany (t:ts) rs = do
  p <- deriveOne t rs
  let (Proof _ _ sgm _) = p
  ps <- deriveMany (map (apply sgm) ts) rs
  return (p:ps)

applyRule :: Substitution s => s -> Rule -> Rule
applyRule s (R rn t ts) = R rn (t <. s) (map (apply s) ts)


-- r = R "A1" (Term "f" [Var "q", Var "q"]) []
ax1 = R "Ax1" (Term "f" [lit "a", lit "a"]) []
ax2 = R "Ax2" (Term "f" [lit "a", lit "b"]) []
ax3 = R "Ax3" (Term "f" [lit "b", lit "a"]) []
ax4 = R "Ax4" (Term "f" [lit "b", lit "c"]) []
ax5 = R "Ax5" (Term "f" [lit "c", lit "d"]) []
ax6 = R "Ax6" (Term "f" [Term "g" [lit "a"], Term "g" [lit "d"]]) []
axioms = [ax2,ax4,ax5]
rl1 = R "Ru1" (Term "f" [Var "x", Var "y"]) [Term "f" [Var "x", Var "z"],Term "f" [Var "z", Var "y"]]
rl2 = R "Ru2" (Term "f" [Term "g" [Var "x"], Term "g" [Var "y"]]) [Term "f" [Var "x", Var "y"]]
rl3 = R "Ru2" (Term "f" [Term "h" [Var "x",Var "y"]]) [Term "f" [Var "x", Var "y"]]

rs1 = axioms ++ [rl2,rl1]
t1 = Term "f" [Var "x", Var "x"]
t2 = Term "f" [Term "g" [Var "x"], Term "g" [Var "y"]]
t3 = Term "f" [lit "a", lit "d"]
t4 = Term "f" [Term "g" [lit "a"], Term "g" [lit "d"]]
t5 = Term "f" [lit "a", Var "x"]
t6 = Term "f" [Var "x", lit "b"]
t7 = Term "f" [lit "a", lit "b"]
t8 = Term "f" [Term "g" [lit "a"], Var "x"]
t9 = Term "f" [Term "g" [lit "a"], Term "g" [Var "y"]]

instance Show Rule where
  show (R rn t ts) = rn ++ " " ++ show t ++ " -: {" ++ intercalate ", " (map show ts) ++ "}"

instance (Substitution s,Show s) => Show (Proof s) where
  -- show (Proof rn t s ps) = show t ++ " -|" ++ rn ++ " " ++ show ps
  show (Proof rn t s ps) = show t ++ " ~ " ++ show (t <. s) ++ " -|" ++ rn ++ "\x1b[31;90m {" ++ show s ++ "}\x1b[0m " ++ show ps

composeProofSubst :: Substitution s => Proof s -> s
composeProofSubst (Proof _ _ s ps) = foldr compose s (map composeProofSubst ps)
