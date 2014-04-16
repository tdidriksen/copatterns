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
  deriving (Eq, Show)