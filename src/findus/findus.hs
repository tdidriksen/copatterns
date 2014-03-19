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

-- Examples --

root = ERoot [letShrink, letNatPred, dataNat, dataNatList, letStupidNat1, letStupidNat2, letInfRec, letNatPlus]

natBody = TVari [
            ("Z", TUnit), 
            ("S", TTypeVar "Nat")
          ]

dataNat = EData "Nat" nat
nat = TRec "Nat" (natBody)

natListBody = TVari [
                ("nil", TUnit),
                ("cons", TTuple [nat, (TTypeVar "NatList")])
              ]

dataNatList = EData "NatList" natList
natList = TRec "NatList" (natListBody)

letNatPlus = ELetFun "plus" (TArr (nat) (TArr nat nat)) natPlus
natPlus = ELam "m" nat (
            ELam "n" nat (
              ECase (EApp (EUnfold nat) (EVar "n")) [
                ("Z", ("()", EVar "m")),
                ("S", ("n'", EApp (EApp (EVar "plus") (EVar "n'")) (EVar "m")))
              ]
            )
          )

letNatPred = ELetFun "pred" (TArr nat nat) natPred
natPred = ELam "n" nat (
            ECase (EApp (EUnfold nat) (EVar "n")) [
              ("Z", ("()", EApp (EFold nat) (ETag "Z" EUnit natBody))),
              ("S", ("n'", EVar "n'"))
            ]
          )

letShrink = ELetFun "shrink" (TArr natList natList) shrink
shrink = ELam "xs" natList (
          ECase (EApp (EUnfold natList) (EVar "xs")) [
            ("nil" , ("[]", (EApp (EFold natList) (ETag "nil" EUnit natListBody)))),
            ("cons", ("x:xs", ETupProj (EVar "x:xs") (ELit (LInt 1)))) 
          ]
        )

letStupidNat1 = ELetFun "stupid1" (TArr nat nat) stupid1
stupid1 = ELam "x" nat (EApp (EVar "stupid2") (EVar "x"))


letStupidNat2 = ELetFun "stupid2" (TArr nat nat) stupid2
stupid2 = ELam "x" nat (EApp (EVar "stupid1") (EVar "x"))

letInfRec = ELetFun "infrec" (TArr nat nat) infRec
infRec = ELam "x" nat (EApp (EVar "infrec") (EVar "x"))
