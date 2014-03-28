module Findus where

type Sym = String 
type Env = [(Sym, Type)]
type Params = [(Sym, Type)]

data Expr 
  = EUnit
  | EVar Sym
  | EApp Expr [Expr]
  | ELit Lit
  | ELet Sym Type (Maybe Params) Expr Expr
  | EIf Expr Expr Expr
  | ETuple [Expr]
  | ETupProj Expr Expr
  | ERecord [(Sym, Expr)]
  | ERecordProj Expr Sym
  | ECase Expr [(Sym, ([Sym], Expr))]
  | ETag Sym [Expr] Type 
  | EFold Type
  | EUnfold Type
  | ERoot [Expr]
  | EData Sym Type
  | EGlobLet Sym Type (Maybe Params) Expr
  deriving (Eq, Show)

data Lit
  = LInt Int
  | LBool Bool
  | LString String
  deriving (Eq, Show)

data Type
  = TUnit
  | TInt
  | TBool
  | TString
  | TArr [Type] Type
  | TTuple [Type]
  | TRecord [(Sym, Type)]
  | TVari [(Sym, [Type])]
  | TRec Sym Type
  | TRecTypeVar Sym
  | TGlobTypeVar Sym
  deriving (Eq)

instance Show Type where
  show TUnit = "Unit"
  show TInt = "Int"
  show TBool = "Bool"
  show TString = "String"
  show (TArr t1 t2) = (showListOf " -> " t1) ++ " -> " ++ (show t2)
  show (TTuple ts) = "Tuple " ++ (showListOf ", " ts)
  show (TRecord ts) = "Record " ++ (showListOf ", " ts)
  show (TVari ts) = "Variant " ++ (showListOf ", " ts)
  show (TRec s t) = s ++ ": (" ++ (show t) ++ ")"
  show (TRecTypeVar s) = "RecTypeVar " ++ s
  show (TGlobTypeVar s) = "GlobalTypeVar " ++ s

showListOf :: Show a => String -> [a] -> String
showListOf d [] = "[]"
showListOf d x = "[" ++ showListOf' d x

showListOf' :: Show a => String -> [a] -> String
showListOf' d [] = "]"
showListOf' d (x : []) = (show x) ++ "]"
showListOf' d (x : xs) = (show x) ++ d ++ showListOf' d xs