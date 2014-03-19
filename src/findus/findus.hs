module Findus where

type Sym = String 
type Env = [(Sym, Type)]

data Expr 
  = EUnit
  | EVar Sym
  | ELam Sym Type Expr
  | EApp Expr Expr
  | ELit Lit
  | ELet Sym Expr Expr
  | EIf Expr Expr Expr
  | ETuple [Expr]
  | ETupProj Expr Expr
  | ERecord [(Sym, Expr)]
  | ERecordProj Expr Sym
  | ECase Expr [(Sym, (Sym, Expr))]
  | ETag Sym Expr Type 
  | EFold Type
  | EUnfold Type
  | ERoot [Expr]
  | EData Sym Type
  | ELetFun Sym Type Expr
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
  | TArr Type Type
  | TTuple [Type]
  | TRecord [(Sym, Type)]
  | TVari [(Sym, Type)]
  | TRec Sym Type
  | TTypeVar Sym
  deriving (Eq, Show)
