module Expr where

type Sym = String 
type Env = [(Sym, Type)]
type Params = [(Sym, Type)]

data Expr 
  = EUnit
  | EVar Sym
  | EApp Expr [Expr]
  | ELet Sym Type (Maybe Params) Expr Expr
  | ECase Expr [(Sym, ([Sym], Expr))]
  | EObserve Type [(Sym, Expr)]
  | ETag Sym [Expr] Type 
  | EFold Type
  | EUnfold Type
  | ERoot [Expr]
  | EData Sym Type
  | ECodata Sym Type
  | EGlobLet Sym Type (Maybe Params) Expr
  deriving (Eq, Show)

data Type
  = TUnit
  | TArr [Type] Type
  | TVari [(Sym, [Type])]
  | TRecInd Sym Type
  | TRecCoind Sym [(Sym, Type)]
  | TRecTypeVar Sym
  | TGlobTypeVar Sym
  deriving (Eq)

instance Show Type where
  show TUnit = "Unit"
  show (TArr t1 t2) = (showListOf " -> " t1) ++ " -> " ++ (show t2)
  show (TVari ts) = "Variant " ++ (showListOf ", " ts)
  show (TRecInd s t) = "Inductive Type " ++ s ++ ": (" ++ (show t) ++ ")"
  show (TRecCoind s t) = "Coinductive Type " ++ s ++ ": (" ++ (show t) ++ ")"
  show (TRecTypeVar s) = "RecTypeVar " ++ s
  show (TGlobTypeVar s) = "GlobalTypeVar " ++ s

showListOf :: Show a => String -> [a] -> String
showListOf d [] = "[]"
showListOf d x = "[" ++ showListOf' d x

showListOf' :: Show a => String -> [a] -> String
showListOf' d [] = "]"
showListOf' d (x : []) = (show x) ++ "]"
showListOf' d (x : xs) = (show x) ++ d ++ showListOf' d xs