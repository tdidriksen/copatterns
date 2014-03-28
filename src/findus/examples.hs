module Examples where

import Findus
import TypeChecker

-- Root Example
rootEnv = case buildRootEnv root of
            Right(l) -> l
root = [dataNatList, letEmpty, letShrink, letNatPred, letStupid1, letStupid2, letInfRec, letNatPlus, dataNat]
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
letNatPlus = EGlobLet "plus" (TArr [TGlobTypeVar "nat", TGlobTypeVar "nat"] (TGlobTypeVar "nat")) (Just ([("n", TGlobTypeVar "nat"), ("m", TGlobTypeVar "nat")])) natPlus
natPlus = ECase (EApp (EUnfold (TGlobTypeVar "nat")) [(EVar "n")]) [
            ("Z", ([], EVar "m")),
            ("S", (["n'"], EApp (EApp (EVar "plus") [(EVar "n'")]) [(EVar "m")]))
          ]

letNatPred = EGlobLet "pred" (TArr [TGlobTypeVar "nat"] (TGlobTypeVar "nat")) (Just [("n", TGlobTypeVar "nat")]) natPred
natPred = ECase (EApp (EUnfold (TGlobTypeVar "nat")) [(EVar "n")]) [
            ("Z", ([], EApp (EFold (TGlobTypeVar "nat")) [(ETag "Z" [] natBody)])),
            ("S", (["n'"], EVar "n'"))
          ]

-- List of natural numbers
natListBody = TVari [
                ("nil", []),
                ("cons", [(TGlobTypeVar "nat"), (TRecTypeVar "natList")])
              ]

dataNatList = EData "natList" natList
natList = TRec "natList" (natListBody)

-- Functions on List of natural numbers
letShrink = EGlobLet "shrink" (TArr [TGlobTypeVar "natList"] (TGlobTypeVar "natList")) (Just [("xs", TGlobTypeVar "natList")])shrink
shrink = ECase (EApp (EUnfold (TGlobTypeVar "natList")) [(EVar "xs")]) [
          ("nil", ([], (EApp (EFold (TGlobTypeVar "natList")) [(ETag "nil" [] natListBody)]))),
          ("cons", (["y", "ys"], (EVar "ys"))) 
        ]

letEmpty = EGlobLet "empty" (TArr [TGlobTypeVar "natList"] (TGlobTypeVar "natList")) (Just [("xs", TGlobTypeVar "natList")]) empty
empty = ECase (EApp (EUnfold (TGlobTypeVar "natList")) [(EVar "xs")]) [
          ("nil", ([], (EApp (EFold (TGlobTypeVar "natList")) [(ETag "nil" [] natListBody)]))),
          ("cons", (["y", "ys"], EApp (EVar "empty") [(EVar "ys")])) 
        ]

-- Misc
letStupid1 = EGlobLet "stupid1" (TArr [nat] nat) (Just [("x", nat)]) stupid1
stupid1 = EApp (EVar "stupid2") [(EVar "x")]

letStupid2 = EGlobLet "stupid2" (TArr [nat] nat) (Just [("x", nat)]) stupid2
stupid2 = EApp (EVar "stupid1") [(EVar "x")]

letInfRec = EGlobLet "infrec" (TArr [nat] nat) (Just [("x", nat)]) infRec
infRec = EApp (EVar "infrec") [(EVar "x")]
