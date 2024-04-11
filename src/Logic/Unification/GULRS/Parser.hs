module Logic.Unification.GULRS.Parser where


import Logic.Unification.GULRS.Syntax


import Text.Parsec hiding (runP)
import Text.Parsec.String (Parser)


nameParser :: Parser Name
nameParser = do
  n <- many1 (alphaNum <|> char '_')
  spaces
  return n


termIntParser :: Parser (Term UnificationVar)
termIntParser = do
  i <- many1 digit
  spaces
  return $ TInt (read i)

termStrParser :: Parser (Term UnificationVar)
termStrParser = TStr <$> nameParser

termVarParser :: Parser (Term UnificationVar)
termVarParser = do
  char '?'
  spaces
  v <- nameParser
  spaces
  return $ Var (MKUnificationVar v)

termQryParser :: Parser (Term UnificationVar)
termQryParser = do
  n <- nameParser
  char '('
  spaces
  ts <- termParser `sepBy` (spaces *> char ',' <* spaces)
  spaces
  char ')'
  spaces
  return $ TQry n ts


termParser :: Parser (Term UnificationVar)
termParser = spaces *> (try termIntParser 
                        <|> try termQryParser 
                        <|> try termVarParser 
                        <|> termStrParser) <* spaces

ruleParser :: Parser (Rule UnificationVar)
ruleParser = do
  n <- nameParser
  spaces
  char '@'
  spaces
  t <- termParser
  spaces
  string "<-"
  spaces
  ts <- termParser `sepBy` (spaces *> char ',' <* spaces)
  spaces
  char ';'
  spaces
  return $ Rule n t ts



runP :: Parser a -> String -> a
runP p s = case parse p "" s of
  Left err -> error $ show err
  Right a -> a

parseRule :: String -> Rule UnificationVar
parseRule = runP ruleParser

parseQuery :: String -> Term UnificationVar
parseQuery = runP termParser

-- runP :: Parser a -> String -> Either ParseError a
-- runP p s = runParser p () s

{--
BobAlice @ knows(bob, alice) <- ;
AliceCarol @ knows(alice, carol) <- ;
Transitive @ knows(?X,?Y) <- knows(?X,?Z), knows(?Z,?Y);
--}

-- data Term a
--   = TInt Int
--   | TStr String
--   | TQry Name [Term a]
--   | Var a

-- data Rule k
--   = Rule { name :: Name
--          , conclusion :: Term k
--          , premises :: [Term k]
--          } 




-- termParser :: Parser (Term UnificationVar)

-- ruleParser :: Parser (Rule UnificationVar)

-- ruleSystemParser :: Parser [Rule UnificationVar]