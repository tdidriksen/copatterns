module Examples where

import Findus
import TypeChecker

-- Root Example
rootEnv = case buildRootEnv root of
            Right(l) -> l
root = [dataNat, dataNatList, letEmpty] -- letShrink, letNatPred, dataNat, dataNatList, letStupidNat1, letStupidNat2, letInfRec, letNatPlus, 
rootExpr = ERoot root
checkRootEx = checkRoot rootExpr
listOfRootEx = case checkRootEx of
                 Right(k) -> k
                 Left(_) -> []
-- Natural numbers
natBody = TVari [
            ("Z", []), 
            ("S", [TRecTypeVar "nat"])
          ]

dataNat = EData "nat" nat
nat = TRec "nat" (natBody)

-- Functions on Nats
letNatPlus = ELetFun "plus" (TArr (TGlobTypeVar "nat") (TArr (TGlobTypeVar "nat") (TGlobTypeVar "nat"))) natPlus
natPlus = ELam "m" (TGlobTypeVar "nat") (
            ELam "n" (TGlobTypeVar "nat") (
              ECase (EApp (EUnfold (TGlobTypeVar "nat")) (EVar "n")) [
                ("Z", ([], EVar "m")),
                ("S", (["n'"], EApp (EApp (EVar "plus") (EVar "n'")) (EVar "m")))
              ]
            )
          )

letNatPred = ELetFun "pred" (TArr (TGlobTypeVar "nat") (TGlobTypeVar "nat")) natPred
natPred = ELam "n" (TGlobTypeVar "nat") (
            ECase (EApp (EUnfold (TGlobTypeVar "nat")) (EVar "n")) [
              ("Z", ([], EApp (EFold (TGlobTypeVar "nat")) (ETag "Z" [] natBody))),
              ("S", (["n'"], EVar "n'"))
            ]
          )

-- List of natural numbers
natListBody = TVari [
                ("nil", []),
                ("cons", [(TGlobTypeVar "nat"), (TRecTypeVar "natList")])
              ]

dataNatList = EData "natList" natList
natList = TRec "natList" (natListBody)

-- Functions on List of natural numbers
letShrink = ELetFun "shrink" (TArr (TGlobTypeVar "natList") (TGlobTypeVar "natList")) shrink
shrink = ELam "xs" (TGlobTypeVar "natList") (
          ECase (EApp (EUnfold (TGlobTypeVar "natList")) (EVar "xs")) [
            ("nil", ([], (EApp (EFold (TGlobTypeVar "natList")) (ETag "nil" [] natListBody)))),
            ("cons", (["y", "ys"], (EVar "ys"))) 
          ]
        )

letEmpty = ELetFun "letEmpty" (TArr (TGlobTypeVar "natList") (TGlobTypeVar "natList")) empty
empty = ELetRec "empty" (TArr (TGlobTypeVar "natList") (TGlobTypeVar "natList")) (ELam "xs" (TGlobTypeVar "natList") (
          ECase (EApp (EUnfold (TGlobTypeVar "natList")) (EVar "xs")) [
            ("nil", ([], (EApp (EFold (TGlobTypeVar "natList")) (ETag "nil" [] natListBody)))),
            ("cons", (["y", "ys"], EApp (EVar "empty") (EVar "ys"))) 
          ]
        )
      ) (ELam "xs" (TGlobTypeVar "natList") (EApp (EVar "empty") (EVar "xs")))

-- Misc
letStupidNat1 = ELetFun "stupid1" (TArr nat nat) stupid1
stupid1 = ELam "x" nat (EApp (EVar "stupid2") (EVar "x"))


letStupidNat2 = ELetFun "stupid2" (TArr nat nat) stupid2
stupid2 = ELam "x" nat (EApp (EVar "stupid1") (EVar "x"))

letInfRec = ELetFun "infrec" (TArr nat nat) infRec
infRec = ELam "x" nat (EApp (EVar "infrec") (EVar "x"))
