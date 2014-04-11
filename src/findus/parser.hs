module Parser where

import Text.Parsec hiding (spaces)
import Text.Parsec.String (Parser)
import qualified Text.Parsec.Expr as Ex
import Lexer
import Expr

spaces = skipMany space >> skipMany newline

-- let x : int = 1 in x + 1 end
-- let f (x : int, y : int) : int = x + y in f 1 1 end
letin :: Parser Expr
letin = do
  reserved "let"
  x <- identifier
  ps <- optionMaybe $ parens $ sepBy idenannotation (char ',' >> spaces)
  reservedOp ":"
  t <- ty
  reservedOp "="
  e1 <- expr
  reserved "in"
  e2 <- expr
  return $ ELet x t ps e1 e2

letglob :: Parser Expr
letglob = do
  reserved "let"
  x <- identifier
  ps <- optionMaybe $ parens $ sepBy idenannotation (char ',' >> spaces)
  reservedOp ":"
  t <- ty
  reservedOp "="
  e <- expr
  return $ EGlobLet x t ps e

  {-
  case x : nat of
    Z -> Z ;
    S (n : nat) -> n

  case xs : natList of
    nil -> Z ;
    cons y ys -> y
  -}

inductivecase :: Parser Expr
inductivecase = do
  reserved "case"
  x <- exprannotation
  reserved "of"
  cs <- sepBy1 casematch (spaces >> char ';' >> spaces)
  return $ ECase (EApp (EUnfold (snd x)) [fst x]) cs

casematch :: Parser (Sym, ([Sym], Expr))
casematch = do
  x <- many1 identifier
  reservedOp "->"
  e <- expr
  case x of
    x : xs -> return $ (x, (xs, e))
   
{-
  observe natStream as 
    head -> Z ;
    tail -> tail ns
-}

observe :: Parser Expr
observe = do
  reserved "observe"
  t <- ty
  reserved "as"
  os <- sepBy1 observation (spaces >> char ';' >> spaces)
  return $ EObserve t os

observation :: Parser (Sym, Expr)
observation = do
  x <- identifier
  reservedOp "->"
  e <- expr
  return (x, e)

{-
data nat = 
         Z 
       | S nat 
-}

inductivedata :: Parser Expr
inductivedata = do
  reserved "data"
  x <- identifier
  reservedOp "="
  cs <- braces $ sepBy1 (dataconstructor x) (spaces >> char '|' >> spaces)
  return $ EData x (TRecInd x (TVari cs))

dataconstructor :: String -> Parser (Sym, [Type])
dataconstructor n = do
  x <- identifier
  ts <- sepBy ((try $ rectypevar n) <|> ty) spaces
  return (x, ts)

{-
codata natStream = 
    head nat
  | tail natStream
-}

codata :: Parser Expr
codata = do
  reserved "codata"
  x <- identifier
  reservedOp "="
  ds <- braces $ sepBy1 (codatadestructor x) (spaces >> char '|' >> spaces)
  return $ ECodata x (TRecCoind x ds)

codatadestructor :: String -> Parser (Sym, Type)
codatadestructor n = do
  x <- identifier
  ts <- ((try $ rectypevar n) <|> ty)
  return (x, ts)

exprannotation :: Parser (Expr, Type)
exprannotation = do
  e <- expr
  reservedOp ":"
  t <- ty
  return (e, t)

idenannotation :: Parser (Sym, Type)
idenannotation = do
  x <- identifier
  reservedOp ":"
  t <- ty
  return (x, t)

funapp :: Parser Expr
funapp = do
  f <- exprtail
  spaces
  as <- parens $ sepBy1 expr (spaces >> char ',' >> spaces)
  return $ EApp f as

var :: Parser Expr
var = do
  x <- identifier
  return $ EVar x

unittype :: Parser Type
unittype = spaces >> string "Unit" >> spaces >> (return TUnit)

unitexpr :: Parser Expr
unitexpr = spaces >> string "()" >> spaces >> (return EUnit)

globaltypevar :: Parser Type
globaltypevar = do
  x <- identifier
  return $ TGlobTypeVar x

ty :: Parser Type
ty = (try unittype) <|> globaltypevar <|> arrowType

rectypevar :: String -> Parser Type
rectypevar s = string s >> (return $ TRecTypeVar s)

arrowType :: Parser Type
arrowType = do
    ts <- parens $ sepBy1 ty (reservedOp "->")
    case reverse ts of
      x : xs -> return $ TArr (reverse xs) x

expr :: Parser Expr
expr = try funapp
   <|> exprtail 

exprtail :: Parser Expr
exprtail = (try letin)
   <|> letglob
   <|> inductivecase
   <|> observe
   <|> inductivedata
   <|> codata
   <|> unitexpr
   <|> try var

prog :: Parser Expr
prog = do
  es <- sepBy expr spaces
  eof
  return $ ERoot es

readExpr :: String -> Either ParseError Expr
readExpr input = parse prog "findus" input

letExample = "let x : (nat -> Unit) = Z in S (Z)"

letGlobExample1 = "let x : Unit = f (Z)"
letGlobExample2 = "let y : Unit = x (S (Z))" 

letFunExample = "let f (x : int, y : int) : int = () in ()"

caseExample = "case xs : natList of " ++
    "nil -> Z ;" ++
    "cons y ys -> S Z"

observeExample = "observe natStream as " ++ 
    "head -> Z;" ++
    "tail -> fib"

natEx = "data nat = {" ++
         "Z " ++
       "| S nat}"

dataNatListExample = "data natList = " ++
                      "nil" ++
                      "cons nat natList"

natStreamEx = "codata natStream = " ++
   " {head nat" ++
  "| tail natStream}"

testEx = unlines [natEx, natStreamEx, letExample]