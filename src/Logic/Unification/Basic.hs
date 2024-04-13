{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE NamedFieldPuns #-}

module Logic.Unification.Basic where


import Logic.Unification

import Logic.Proof

import qualified Data.Map as Map
import Data.Map (Map)

import Control.Safe
import Data.List (find, intercalate)
import Control.Monad (guard)


import qualified Logic.Unification.GULRS.Syntax as GULRS
import qualified Logic.Unification.GULRS.Parser as GURLS.Parser


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

fromList :: Ord v => [(v,Term v)] -> Subst v
fromList = foldr (compose . uncurry mapsTo) empty


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
  deriving (Eq, Ord)

mkEntailJ :: RuleSystem v -> Term v -> EntailJ v
mkEntailJ rs g = EntailJ rs g (Rule "Ax" g []) empty

safeUnify :: Ord v => Term v -> Term v -> Maybe (Subst v)
safeUnify t t' = do
  σ <- safe $ unifyOne t t'
  guard $ t <. σ == t' <. σ
  return σ

applySystem :: Ord v => RuleSystem v -> Term v -> [(Rule v,Subst v)]
applySystem rs t = [(r,σ) | r <- rs, Just σ <- [safeUnify t (conclusionR r)]]

applyRuleSubst :: Ord v => Subst v -> Rule v -> (Term v,[Term v])
applyRuleSubst σ (Rule _ c ps) = (c <. σ, map (apply σ) ps)

ppTerm :: Show v => Term v -> String
ppTerm (Var v) = show v
ppTerm (Term k ts) = k ++ "(" ++ intercalate "," (map ppTerm ts) ++ ")"

ppSubstitution :: Show v => Subst v -> String
ppSubstitution σ = "{" ++ intercalate "," (map (\(v,t) -> show v ++ " -> " ++ ppTerm t) $ Map.toList σ) ++ "}"

instance Show v => Show (EntailJ v) where
  show (EntailJ rs g r s) = " |- " ++ ppTerm g ++ " " ++ ppSubstitution s


type BEntailJ = EntailJ Name

instance Ord v => Explain (EntailJ v) where
  premises (EntailJ rs t (Rule n c []) σ) | t == c <. σ = [[]]
                                          | Just σ' <- safe (unifyOne t (c <. σ)) = [[EntailJ rs (c <. σ <. σ') (Rule n c []) (σ' <.> σ)]]
                                          | otherwise = []
  premises (EntailJ rs g rl s) = [mkPs r s' | (r,s') <- rules]
    where rules = [(r,s) | (r,Just s) <- ruleTrials]
          ruleTrials = map (\r -> (r,safeUnify $ conclusionR r <. s)) rs
          safeUnify  = safe . unifyOne g
          mkPs r s' | [] <- premisesR r = [EntailJ rs (conclusionR r <. s <. s') r (s' <.> s)] -- [EntailJ rs (conclusionR r <. s <. s') r s']
                    | otherwise         = [EntailJ rs (p <. s <. s') r (s' <.> s) | p <- premisesR r]

  -- comeback (EntailJ rs g r s) [] = EntailJ rs (conclusionR r <. s) r s
  comeback (EntailJ rs g r s) ps = EntailJ rs (g <. s') r s'
    where ss = map (bindings . conclusion) ps
          s' = foldr compose s ss

  proofs :: EntailJ v -> [Proof (EntailJ v)]
  proofs j@(EntailJ {system = rs, goal = t, rule = r, bindings = σ}) = do
    (r'@(Rule n c ps),σ') <- applySystem rs t
    case applyRuleSubst σ' r' of
      (c',[]) -> return $ Proof (j {goal = t <. σ', bindings = σ' <.> σ}) []
      (c',ps') -> do
        let pspfss = map proofs [j {goal = p,rule = Rule n c ps,bindings = σ'} | p <- ps']
        -- let pspfss = do
        --       p <- ps'
        --       return $ proofs $ EntailJ rs p r' σ'
        let pspfs = sequence pspfss
        psfs <- pspfs
        let pjs = map conclusion psfs
        let pjsubs = map bindings pjs
        let s = foldr compose σ pjsubs
        return $ Proof (j {goal = t <. s, bindings = s}) psfs
    -- when (null ps') 
    -- let pspfss = map proofs [j {goal = p,rule = Rule n c ps,bindings = σ'} | p <- ps']
    -- let pspfs = sequence pspfss
    -- psfs <- pspfs
    -- let pjs = map conclusion psfs

    -- return $ Proof j psfs
    -- if null ps
    --   then return $ Proof 
  -- proofs (EntailJ rs t (Rule n c []) σ) = undefined

-- r1 = Rule "Ax1" (Term "P" [Var "x"]) []
-- r2 = Rule "R1" (Term "Q" [Var "x",Var "y"]) [Term "P" [Var "x"],Term "P" [Var "y"]]
-- rs1 = [r1,r2]
-- ej1 = EntailJ rs1 (Term "Q" [Term "f" [lit "a"],Var "b"]) r1

r1 = Rule "AliceBob" (Term "friends" [lit "Alice",lit "Bob"]) []
r2 = Rule "BobCharlie" (Term "friends" [lit "Bob",lit "Charlie"]) []
r3 = Rule "FriendsTrans" (Term "friends" [Var "x",Var "y"]) [Term "friends" [Var "x",Var "z"],Term "friends" [Var "z",Var "y"]]
rs1 = [r1,r2,r3]
ej1 = EntailJ rs1 (Term "friends" [lit "Alice",lit "Charlie"]) r3 empty
ej2 = EntailJ rs1 (Term "friends" [lit "Alice",Var "z"]) r3 empty
ej3 = EntailJ rs1 (Term "friends" [lit "Alice",Var "c"]) r3 empty
ej4 = mkEntailJ rs1 (Term "friends" [lit "Alice",Var "c"])
-- class Substitution s where
--   {-# MINIMAL empty, mapsTo, apply, compose #-}
--   empty :: s
--   mapsTo :: Name -> Term -> s
--   apply :: s -> Term -> Term
--   -- (<.) = flip apply
--   compose :: s -> s -> s
--   -- (<.>) = compose
--   -- (t <. tau) <. sgm = t <. (sgm <.> tau)



toGurls :: Term v -> GULRS.Term v
toGurls (Var v) = GULRS.Var v
toGurls (Term k ts) = GULRS.TQry k (map toGurls ts)

toGurlsRule :: Rule v -> GULRS.Rule v
toGurlsRule (Rule n c ps) = GULRS.Rule n (toGurls c) (map toGurls ps)

toGurlsSystem :: RuleSystem v -> GULRS.RuleSystem v
toGurlsSystem = map toGurlsRule

fromGurls :: GULRS.Term v -> Term v
fromGurls (GULRS.Var v) = Var v
fromGurls (GULRS.TQry k ts) = Term k (map fromGurls ts)
fromGurls (GULRS.TInt i) = Term (show i) []
fromGurls (GULRS.TStr s) = Term s []

fromGurlsRule :: GULRS.Rule v -> Rule v
fromGurlsRule (GULRS.Rule n c ps) = Rule n (fromGurls c) (map fromGurls ps)

fromGurlsSystem :: GULRS.RuleSystem v -> RuleSystem v
fromGurlsSystem = map fromGurlsRule



