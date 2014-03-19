module Examples where

import Findus
import TypeChecker

-- Root Example
root = ERoot [letShrink, letNatPred, dataNat, dataNatList, letStupidNat1, letStupidNat2, letInfRec, letNatPlus]
checkRootEx = checkRoot root

-- Natural numbers
natBody = TVari [
            ("Z", TUnit), 
            ("S", TTypeVar "Nat")
          ]

dataNat = EData "Nat" nat
nat = TRec "Nat" (natBody)

-- Functions on Nats
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

-- List of natural numbers
natListBody = TVari [
                ("nil", TUnit),
                ("cons", TTuple [nat, (TTypeVar "NatList")])
              ]

dataNatList = EData "NatList" natList
natList = TRec "NatList" (natListBody)

-- Functions on List of natural numbers
letShrink = ELetFun "shrink" (TArr natList natList) shrink
shrink = ELam "xs" natList (
          ECase (EApp (EUnfold natList) (EVar "xs")) [
            ("nil" , ("[]", (EApp (EFold natList) (ETag "nil" EUnit natListBody)))),
            ("cons", ("x:xs", ETupProj (EVar "x:xs") (ELit (LInt 1)))) 
          ]
        )

-- Misc
letStupidNat1 = ELetFun "stupid1" (TArr nat nat) stupid1
stupid1 = ELam "x" nat (EApp (EVar "stupid2") (EVar "x"))


letStupidNat2 = ELetFun "stupid2" (TArr nat nat) stupid2
stupid2 = ELam "x" nat (EApp (EVar "stupid1") (EVar "x"))

letInfRec = ELetFun "infrec" (TArr nat nat) infRec
infRec = ELam "x" nat (EApp (EVar "infrec") (EVar "x"))