module Examples where

import Expr
import TypeChecker
import Control.Applicative

-- Root Example
rootEnv = case buildRootEnv root of
            Right(l) -> l
root = [dataNat, codataNatStream, letFib, letNatPlus, letZipWithPlus, dataNatList, letEmpty, letShrink, letNatPred, letStupid1, letStupid2, letInfRec]
rootExpr = ERoot root
checkRootEx = checkRoot rootExpr
listOfRootEx = case checkRootEx of
                 Right(k) -> k
                 Left(_) -> []
listOfTypes = pure (map getTypeAnno) <*> checkRootEx

-- Natural numbers
natBody = TVari [
            ("Z", []), 
            ("S", [TRecTypeVar "nat"])
          ]

dataNat = DData "nat" nat
nat = TRecInd "nat" (natBody)

-- Functions on Nats
letNatPlus = DGlobLet "plus" (TArr [TGlobTypeVar "nat", TGlobTypeVar "nat"] (TGlobTypeVar "nat")) (Just ([("n", TGlobTypeVar "nat"), ("m", TGlobTypeVar "nat")])) natPlus
natPlus = ECase (EApp (EUnfold (TGlobTypeVar "nat")) [(EVar "n")]) [
            ("Z", ([], EVar "m")),
            ("S", (["n'"], EApp (EVar "plus") [(EVar "n'"), (EVar "m")]))
          ]

letNatPred = DGlobLet "pred" (TArr [TGlobTypeVar "nat"] (TGlobTypeVar "nat")) (Just [("n", TGlobTypeVar "nat")]) natPred
natPred = ECase (EApp (EUnfold (TGlobTypeVar "nat")) [(EVar "n")]) [
            ("Z", ([], EVar "Z")),
            ("S", (["n'"], EVar "n'"))
          ]

-- List of natural numbers
natListBody = TVari [
                ("nil", []),
                ("cons", [(TGlobTypeVar "nat"), (TRecTypeVar "natList")])
              ]

dataNatList = DData "natList" natList
natList = TRecInd "natList" (natListBody)

-- Functions on List of natural numbers
letShrink = DGlobLet "shrink" (TArr [TGlobTypeVar "natList"] (TGlobTypeVar "natList")) (Just [("xs", TGlobTypeVar "natList")]) shrink
shrink = ECase (EApp (EUnfold (TGlobTypeVar "natList")) [(EVar "xs")]) [
          ("nil", ([], (EApp (EFold (TGlobTypeVar "natList")) [(ETag "nil" [] natListBody)]))),
          ("cons", (["y", "ys"], (EVar "ys"))) 
        ]

letEmpty = DGlobLet "empty" (TArr [TGlobTypeVar "natList"] (TGlobTypeVar "natList")) (Just [("xs", TGlobTypeVar "natList")]) emptyList
emptyList = ECase (EApp (EUnfold (TGlobTypeVar "natList")) [(EVar "xs")]) [
          ("nil", ([], (EApp (EFold (TGlobTypeVar "natList")) [(ETag "nil" [] natListBody)]))),
          ("cons", (["y", "ys"], EApp (EVar "empty") [(EVar "ys")])) 
        ]

-- Stream Nat
natStreamBody = [
                  ("head", TGlobTypeVar "nat"),
                  ("tail", TRecTypeVar "natStream")
                ]

codataNatStream = DCodata "natStream" natStream
natStream = TRecCoind "natStream" natStreamBody

letZipWithPlus = DGlobLet "zipWithPlus" (TArr [(TGlobTypeVar "natStream"), (TGlobTypeVar "natStream")] (TGlobTypeVar "natStream")) (Just [("xs", (TGlobTypeVar "natStream")), ("ys", (TGlobTypeVar "natStream"))]) zipWithPlus
zipWithPlus = EObserve (TGlobTypeVar "natStream")
                [
                  ("head", EApp (EVar "plus")[
                      (EApp (EVar "head") [EVar "xs"]),
                      (EApp (EVar "head") [EVar "ys"])
                    ]),
                  ("tail", EApp (EVar "zipWithPlus") [
                      (EApp (EVar "tail") [EVar "xs"]),
                      (EApp (EVar "tail") [EVar "ys"])
                    ])
                ]

letFib = DGlobLet "fib" (TGlobTypeVar "natStream") Nothing fib
fib = EObserve (TGlobTypeVar "natStream") 
        [
          ("head", EVar "Z"),
          ("tail", EObserve (TGlobTypeVar "natStream")
                     [
                       ("head", EApp (EVar "S") [EVar "Z"]),
                       ("tail", EApp (EVar "zipWithPlus") 
                          [
                            EVar "fib", 
                            (EApp (EVar "tail") [EVar "fib"])
                          ]
                        )
                     ]
                  )
        ]

-- Misc
letStupid1 = DGlobLet "stupid1" (TArr [nat] nat) (Just [("x", nat)]) stupid1
stupid1 = EApp (EVar "stupid2") [(EVar "x")]

letStupid2 = DGlobLet "stupid2" (TArr [nat] nat) (Just [("x", nat)]) stupid2
stupid2 = EApp (EVar "stupid1") [(EVar "x")]

letInfRec = DGlobLet "infrec" (TArr [nat] nat) (Just [("x", nat)]) infRec
infRec = EApp (EVar "infrec") [(EVar "x")]