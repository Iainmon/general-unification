module Logic.Unification.GULRS.Syntax where
import Control.Applicative
import Control.Monad
import Data.List (intercalate)

{--
BobAlice @ knows(bob, alice) <- ;
AliceCarol @ knows(alice, carol) <- ;
Transitive @ knows(?X,?Y) <- knows(?X,?Z), knows(?Z,?Y);
--}
type Name = String

newtype MetaVar = MKMetaVar Name
  deriving (Eq, Ord, Show)


newtype UnificationVar = MKUnificationVar Name
  deriving (Eq, Ord)

instance Show UnificationVar where
  show (MKUnificationVar n) = n



unMetaVar :: MetaVar -> Name
unMetaVar (MKMetaVar n) = n

unUnificationVar :: UnificationVar -> Name
unUnificationVar (MKUnificationVar n) = n

data Term a
  = TInt Int
  | TStr String
  | TQry Name [Term a]
  | Var a
  deriving (Eq, Ord, Functor, Foldable, Traversable)

freeVars :: Ord a => Term a -> [a]
freeVars (TInt _) = []
freeVars (TStr _) = []
freeVars (TQry _ ts) = concatMap freeVars ts
freeVars (Var a) = [a]


instance Show a => Show (Term a) where
  show (TInt i) = show i
  show (TStr s) = show s
  show (TQry n ts) = n ++ "(" ++ (intercalate "," (map show ts)) ++ ")"
  show (Var a) = show a

instance Applicative Term where
  pure :: a -> Term a
  pure = Var
  (<*>) :: Term (a -> b) -> Term a -> Term b
  (<*>) = ap

instance Monad Term where
  (>>=) :: Term a -> (a -> Term b) -> Term b
  (>>=) (TInt i) _ = TInt i
  (>>=) (TStr s) _ = TStr s
  (>>=) (TQry n ts) f = TQry n (map (>>= f) ts)
  (>>=) (Var a) f = f a


andThen :: (a -> Term b) -> Term a -> Term b
andThen = flip (>>=)


data Rule k
  = Rule { name :: Name
         , conclusion :: Term k
         , premises :: [Term k]
         } deriving (Eq, Ord)
         
mkAxiom :: Name -> Term k -> Rule k
mkAxiom n c = Rule n c []


instance Show k => Show (Rule k) where
  show (Rule n c ps) = "[ " ++ show c ++ " =| " ++ (intercalate ", " (map show ps)) ++ " ]"

type RuleSystem k = [Rule k]
