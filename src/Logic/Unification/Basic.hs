{-# LANGUAGE PatternSynonyms #-}


module Logic.Unification.Basic where


import Logic.Unification

import Logic.Proof

import qualified Data.Map as Map
import Data.Map (Map)

import Control.Safe
import Data.List (find)



type Name = String

type Term v = UTerm Name v

pattern Var :: v -> Term v
pattern Var v = UVar v
pattern Term k ts = UTerm k ts


-- Basic term type
type BTerm = Term Name


lit :: Show k => k -> BTerm
lit = Lit . show

occurs :: Eq v => v -> UTerm k v -> Bool
occurs v (UVar v') = v == v'
occurs v (Term _ ts) = any (occurs v) ts

subst :: Eq v => v -> UTerm k v -> (UTerm k v -> UTerm k v)
(v `subst` s) (UVar v') | v == v'    = s
                        | otherwise  = UVar v'
(v `subst` s) (Term f ts)           = Term f (map (v `subst` s) ts)


type Subst v = Map v (Term v)

empty :: Subst v
empty = Map.empty

mapsTo :: v -> Term v -> Subst v
mapsTo = Map.singleton

apply :: Ord v => Subst v -> Term v -> Term v
apply σ (Term f ts) = Term f (map (apply σ) ts)
apply σ (Var x) | Just t <- Map.lookup x σ = t
                | otherwise                = Var x

compose σ τ = (Map.map (apply σ) τ) `Map.union` (σ \\ τ)
  where (\\) = Map.difference

(<.) :: Ord v => Term v -> Subst v -> Term v
(<.) = flip apply

(<.>) :: Ord v => Subst v -> Subst v -> Subst v
(<.>) = compose

ammend :: Ord v => Subst v -> v -> Term v -> Subst v
ammend σ x t = σ <.> mapsTo x t

unifyOne (Var x) t | not (x `occurs` t) = mapsTo x t
unifyOne t@(Term _ _) (Var x) | not (x `occurs` t) = mapsTo x t -- Not in the original (Mar 2)
unifyOne (Term f ts) (Term g ss) | f == g = unifyMany (zip ts ss)
unifyOne t s | t == s = empty
unifyOne (Var x) t | x `occurs` t = error "unifyOne: circularity"
unifyOne t (Var x) | x `occurs` t = error "unifyOne: circularity"
unifyOne _ _ = error "unifyOne: no unifier"

unifyMany [] = empty
unifyMany ((t,s):ts) = σ1 <.> σ2
  where σ2 = unifyMany ts
        σ1 = unifyOne (apply σ2 t) (apply σ2 s)
        bimap f (x,y) = (f x, f y)


data Rule v 
  = Rule { nameR :: Name
         , conclusionR :: Term v
         , premisesR :: [Term v]
         }
  deriving (Show, Eq, Ord, Functor)
type BRule = Rule Name

type RuleSystem v = [Rule v]
type BRuleSystem = RuleSystem Name

lookupRule :: Name -> RuleSystem v -> Maybe (Rule v)
lookupRule n = find (\r -> n == nameR r)

data EntailJ v
  = EntailJ { system :: RuleSystem v
            , goal :: Term v
            , rule :: Rule v -- bindings can be found via the rule and goal
            , bindings :: Subst v
            }
  deriving (Eq, Ord, Functor)

instance Show v => Show (EntailJ v) where
  show (EntailJ rs g r) = show g ++ " " ++ nameR r


type BEntailJ = EntailJ Name

instance Ord v => Explain (EntailJ v) where
  premises (EntailJ rs g _ s) = [[EntailJ rs (p <. s' <. s) r (s' <.> s) | p <- premisesR r] | (r,s') <- rules]
    where rules = [(r,s) | (r,Just s) <- ruleTrials]
          ruleTrials = map (\r -> (r,safeUnify $ conclusionR r)) rs
          safeUnify  = safe . unifyOne g

  comeback (EntailJ rs g r s) ps = EntailJ rs (g <. s) r (s <.> s')
    where ss = map (bindings . conclusion) ps
          s' = foldr (<.>) empty ss

-- r1 = Rule "Ax1" (Term "P" [Var "x"]) []
-- r2 = Rule "R1" (Term "Q" [Var "x",Var "y"]) [Term "P" [Var "x"],Term "P" [Var "y"]]
-- rs1 = [r1,r2]
-- ej1 = EntailJ rs1 (Term "Q" [Term "f" [lit "a"],Var "b"]) r1

r1 = Rule "AliceBob" (Term "friends" [lit "Alice",lit "Bob"]) []
r2 = Rule "BobCharlie" (Term "friends" [lit "Bob",lit "Charlie"]) []
r3 = Rule "FriendsTrans" (Term "friends" [Var "x",Var "y"]) [Term "friends" [Var "x",Var "z"],Term "friends" [Var "z",Var "y"]]
rs1 = [r1,r2,r3]
ej1 = EntailJ rs1 (Term "friends" [lit "Alice",lit "Charlie"]) r1


-- class Substitution s where
--   {-# MINIMAL empty, mapsTo, apply, compose #-}
--   empty :: s
--   mapsTo :: Name -> Term -> s
--   apply :: s -> Term -> Term
--   -- (<.) = flip apply
--   compose :: s -> s -> s
--   -- (<.>) = compose
--   -- (t <. tau) <. sgm = t <. (sgm <.> tau)



