module Findus where

import Prelude

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
  | EPair Expr Expr
  | EFst Expr
  | ESnd Expr
  | ETuple [Expr]
  | ETupProj Expr Expr
  | ERecord [(Sym, Expr)]
  | ERecordProj Expr Sym
  | ECase Expr [(Sym, (Sym, Expr))]
  | ETag Sym Expr Type
  | EFix Expr
  | EFold Type
  | EUnfold Type
  deriving (Eq, Show)

data Lit
  = LInt Int
  | LBool Bool
  | LString String
  deriving (Eq, Show)

data Type
  = TUnit
  | TId Sym
  | TInt
  | TBool
  | TString
  | TArr Type Type
  | TProd Type Type
  | TTuple [Type]
  | TRecord [(Sym, Type)]
  | TVari [(Sym, Type)]
  | TRec Sym Type
  | TTypeVar Sym
  deriving (Eq, Show)

-- Test --

natBody = TVari [
            ("Z", TUnit), 
            ("S", TTypeVar "Nat")
          ]

nat = TRec "Nat" (natBody)

natListBody = TVari [
                ("nil", TUnit),
                ("cons", TTuple [nat, (TTypeVar "NatList")])
              ]

natList = TRec "NatList" (natListBody)

natPred = ELam "n" nat (
            ECase (EApp (EUnfold nat) (EVar "n")) [
              ("Z", ("()", EApp (EFold nat) (ETag "Z" EUnit natBody))),
              ("S", ("n", EVar "n"))
            ]
          )

shrink = ELam "xs" natList (
          ECase (EApp (EUnfold natList) (EVar "xs")) [
            ("nil" , ("[]", (EApp (EFold natList) (ETag "nil" EUnit natListBody)))),
            ("cons", ("x:xs", ETupProj (EVar "x:xs") (ELit (LInt 1)))) 
          ]
        )


