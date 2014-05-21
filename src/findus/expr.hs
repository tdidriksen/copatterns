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
  | ERoot [Defi] 
  deriving (Eq, Show)

data Defi
  = DData Sym Type
  | DCodata Sym Type
  | DGlobLet Sym Type (Maybe Params) Expr
  deriving (Eq, Show)

data Type
  = TUnit
  | TArr [Type] Type
  | TVari [(Sym, [Type])]
  | TRecInd Sym Type
  | TRecCoind Sym [(Sym, Type)]
  | TRecTypeVar Sym
  | TGlobTypeVar Sym
  deriving (Show)

instance Eq Type where
  TUnit          == TUnit           = True
  TArr      ts t == TArr ts' t'     = (ts == ts') && t == t'
  TVari     xs   == TVari ys        = xs == ys
  TRecInd    s t == TRecInd s' t'   = s == s'
  TRecCoind  s t == TRecCoind s' t' = s == s'
  TRecTypeVar  s == TRecTypeVar s'  = s == s'
  TGlobTypeVar s == TGlobTypeVar s' = s == s'
  _ == _ = False