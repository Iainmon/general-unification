module Logic.Unification.GULRS.Unification where

import Control.Applicative
import Control.Monad
-- import Control.Monad.Unify.Trans hiding (Name)
import Control.Monad.Trans.State
-- import Control.Monad.Trans.Class ( MonadTrans(lift) ) 

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set


import Data.List (intercalate)

import Logic.Unification.GULRS.Syntax
import Logic.Unification.GULRS.Parser (parseRule, parseQuery)
import Data.Maybe (fromMaybe)
import qualified Debug.Trace as Trace
import Data.Char (digitToInt,ord,chr)

class (Ord k,Show k) => UVar k where
  fresh :: k -> Int -> k

instance UVar UnificationVar where
  fresh (MKUnificationVar k) i = MKUnificationVar (k ++ [chr (ord '\x2080' + digitToInt d) | d <- show i])

type Substitution k = Map k (Term k)

ppSubstitution :: Show k => Substitution k -> String
ppSubstitution σ = "{" ++ (intercalate ", " (map (\(k,v) -> show k ++ " -> " ++ show v) (Map.toList σ))) ++ "}"

-- sigma :: Substitution Char
sigma = Map.fromList [('y', Var 'x'), ('x', Var 'a')]
sigma1 = Map.fromList [('y', Var 'x')]
sigma2 = Map.fromList [('x', Var 'a')]

sub :: UVar k => Term k -> Substitution k -> Term k
sub (TQry n ts) σ = TQry n (map (<\> σ) ts)
sub (Var k) σ | Just t <- Map.lookup k σ = t
sub t _ = t

(<\>) :: UVar k => Term k -> Substitution k -> Term k
t <\> σ = sub t σ

(<.>) :: UVar k => Substitution k -> Substitution k -> Substitution k
τ <.> σ = m1 `Map.union` m2
  where m1 = Map.map (\t -> t <\> σ) τ 
        m2 = Map.withoutKeys σ (Map.keysSet τ)  -- Map.filterWithKey (\k _ -> Map.notMember k τ) σ

emptyS :: Substitution k
emptyS = Map.empty

aggregate :: UVar k => [Term k] -> [Term k] -> Substitution k
aggregate [] [] = emptyS
aggregate (t:ts) (s:ss) = u1 <.> (aggregate (map (<\> u1) ts) (map (<\> u1) ss))
  where u1 = t <~> s

(<~>) :: UVar k => Term k -> Term k -> Substitution k
TQry n ts <~> TQry m ss | n == m = aggregate ts ss
TInt i <~> TInt j | i == j = emptyS
TStr s <~> TStr t | s == t = emptyS
Var x <~> Var y | x == y   = emptyS
Var x <~> t | not $ x `elem` freeVars t = Map.singleton x t
t <~> Var x | TQry _ _ <- t, not $ x `elem` freeVars t = Map.singleton x t
t <~> Var x | TInt _ <- t = Map.singleton x t
t <~> Var x | TStr _ <- t = Map.singleton x t
_ <~> _ = emptyS

(<~~>) :: UVar k => Term k -> Term k -> Substitution k
(<~~>) = flip (<~>)

check :: UVar k => Term k -> Term k -> Substitution k -> Bool
check t1 t2 σ = (t1 <\> σ) == (t2 <\> σ)

unify :: UVar k => Term k -> Term k -> Maybe (Substitution k)
unify t1 t2 = if check t1 t2 σ then Just σ else Nothing
  where σ = t1 <~> t2


data Binder k
  = MkBinder { termL :: Term k
             , termR :: Term k
             , binder :: Substitution k
             }
  | MkBinderFail (Term k, Term k, Substitution k)
  deriving (Eq, Ord)

data RuleApp k 
  = MkRuleApp { target :: Term k
              , rule :: Rule k
              , preSubEnv :: Substitution k
              , postSubEnv :: Substitution k
              } deriving (Eq, Ord, Show)

data UnifyState k 
  = MkUnifyState { substitution :: Substitution k
                 , counter :: Int
                 , rules :: RuleSystem k
                 , binders :: [Binder k]
                 , trace :: [RuleApp k]
                 } deriving (Eq, Ord, Show)

emptyUS :: UnifyState k
emptyUS = MkUnifyState emptyS 0 [] [] []

-- UnifyState k -> [(a, UnifyState k)]
type UnifyS k a = StateT (UnifyState k) [] a


binderS :: UVar k => Term k -> Term k -> Substitution k -> UnifyS k (Substitution k)
binderS t1 t2 σ' = do
  σ <- gets substitution
  let b = MkBinder (t1 <\> σ) (t2 <\> σ) σ'
  modify (\s -> s { binders = binders s ++ [b] })
  return (σ <.> σ')

bindFialS :: UVar k => Term k -> Term k -> UnifyS k (Substitution k)
bindFialS t1 t2 = do
  σ <- gets substitution
  let b = MkBinderFail (t1,t2,σ)
  modify (\s -> s { binders = binders s ++ [b] })
  return σ

failedS :: UVar k => UnifyS k Bool
failedS = do
  bs <- gets binders
  return $ any (\b -> case b of
                        MkBinderFail _ -> True
                        _ -> False) bs


unifyS :: UVar k => Term k -> Term k -> UnifyS k (Substitution k)
unifyS t1 t2 = do
  σ <- gets substitution
  let mσ' = unify (t1 <\> σ) (t2 <\> σ)
  case mσ' of
    Nothing -> mzero -- bindFialS t1 t2
    Just σ' -> do 
      binderS t1 t2 σ'
      let σ'' = σ <.> σ'
      modify (\s -> s { substitution = σ'' })
      return σ''

  -- σ' <- fromMaybe mzero (fmap return mσ')
  -- binderS t1 t2 σ'
  -- let σ'' = σ <.> σ'
  -- modify (\s -> s { substitution = σ'' })
  -- return σ''

-- updateS :: UVar k => Substitution k -> UnifyS k ()
-- updateS σ' = do
--   σ <- gets substitution
--   modify (\s -> s { substitution = σ' <.> σ })

unifyRuleS :: UVar k => Term k -> Rule k -> UnifyS k (Rule k)
unifyRuleS t r = do
  c <- gets counter
  modify (\s -> s { counter = c + 1 })
  let r' = instantiateRule c r 
  unifyS t (conclusion r')
  return r'
  where instantiateRule i (Rule n c ps) = Rule n (c <\> σ) (map (<\> σ) ps)
          where σ = Map.fromList [(v,Var (fresh v i)) | v <- freeVars c ++ (concatMap freeVars ps)]

-- not treating each rule check seperately
applyS :: UVar k => Term k -> UnifyS k (Rule k)
applyS t = do
  rs <- gets rules
  σ <- gets substitution
  let rss = map (unifyRuleS t) rs
  x <- msum rss
  return x
  -- modify (\s -> s { substitution = σ })


-- applyS t = do
--   rs <- gets rules
--   σ <- gets substitution
--   r <- lift rs
--   unifyS (conclusion r) t
--   return r


checkS :: UVar k => Term k -> Term k -> UnifyS k Bool
checkS t1 t2 = do
  σ <- gets substitution
  return $ check t1 t2 σ


verifyS :: (Show k,UVar k) => Term k -> UnifyS k (Rule k)
verifyS t = do
  r <- applyS t
  failed <- failedS
  if failed
    then return r
    else do
      sequence_ $ map verifyS (premises r)
      return r

putRuleSystemS :: UVar k => RuleSystem k -> UnifyS k ()
putRuleSystemS rs = modify (\s -> s { rules = rs })

envS :: UVar k => RuleSystem k -> (Term k -> UnifyS k a) -> Term k -> UnifyS k a
envS rs f t = putRuleSystemS rs >> f t

initUnifyState rs = MkUnifyState emptyS 0 rs [] []
  
-- runUnifyS :: UVar k => UnifyS k a -> RuleSystem k -> [(a, Substitution k)]
runUnifyS :: UVar k => UnifyS k a -> RuleSystem k -> [(a, UnifyState k)]
runUnifyS m rs = runStateT m (initUnifyState rs)

execUnifyS :: UVar k => UnifyS k a -> RuleSystem k -> [UnifyState k]
execUnifyS m rs = execStateT m (initUnifyState rs)

binderTraceS :: UVar k => UnifyS k a -> RuleSystem k -> [[Binder k]]
binderTraceS m rs = map binders (execUnifyS m rs)

solutionSubs :: UVar k => Term k -> RuleSystem k -> [Substitution k]
solutionSubs t rs = map substitution (execUnifyS (verifyS t) rs)

solutions :: UVar k => Term k -> RuleSystem k -> [Term k]
solutions t rs = map (t <\>) (solutionSubs t rs)

printBinderTrace :: UVar a => [[Binder a]] -> IO ()
printBinderTrace = mapM_ (\bs -> putStrLn ((intercalate "\n" (map (("  "++) . show) bs) ++ "\n")))


instance UVar k => Show (Binder k) where
  show (MkBinder t1 t2 σ) = show t1 ++ " ~ " ++ show t2 ++ " => " ++ ppSubstitution σ
  show (MkBinderFail (t1,t2,σ)) = ppSubstitution σ ++ " => " ++ show t1 ++ " ~/~ " ++ show t2 ++ " | " ++ show (t1 <\> σ) ++ " ~ " ++ show (t2 <\> σ)

f rs m qs = mapM_ (\(r,s) -> print $ (conclusion r, premises r, substitution s)) $ flip runUnifyS rs $ m $ parseQuery qs







-- good(X) :- kind(X), pure(X).


{--
{ } => good(iain) ~ good(X) { X -> iain }

{ X -> 2 } => X is 2
{ } => X ~ 42 => { X -> 42 }
{ X -> 42 } => 
--}

{--
R1 @ kind(iain).
R2 @ pure(iain).
R3 @ good(X) :- kind(X), pure(X).

?- good(iain).

good(iain) <~> good(X) => { X -> iain }
{ X -> iain } kind(X)
kind(X) <\> { X -> iain } <~> kind(iain)
--}

merge :: UVar k => Term k -> Term k -> Substitution k -> Maybe (Substitution k)
merge t1 t2 σ = if check t1' t2' σ' then Just σ' else Nothing
  where σ' = t1' <~> t2'
        t1' = t1 <\> σ
        t2' = t2 <\> σ

step :: UVar k => Term k -> Term k -> Substitution k -> Maybe (Substitution k)
step t1 t2 σ = if check t1' t2 σ' then Just (σ' <.> σ) else Nothing
  where σ' = t1' <~> t2
        t1' = t1 <\> σ

applyRule :: UVar k => Term k -> Rule k -> Substitution k -> Maybe (Substitution k, [Term k])
applyRule t (Rule _ c ps) σ | Just σ' <- merge c t σ = Just (σ',ps)
applyRule _ _ _ = Nothing


-- prove :: UVar k => Substitution k -> Term k -> Rule k -> 
-- -- prove σ t (Rule _ c []) | check c t σ then Just σ else Nothing
-- prove σ t (Rule _ c ps) = 
--   where σ' = c <~> (t <\> σ)

  -- () <- return $ Trace.trace (show t ++ show σ) ()
  -- guard $ and (map (\p -> not $ check t p σ) (premises r))