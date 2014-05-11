module TestPrograms where

import Expr

-- Natural numbers

natBody :: Type
natBody = TVari [
            ("Z", []), 
            ("S", [TRecTypeVar "nat"])
          ]
natRec :: Type
natRec = TRecInd "nat" natBody

nat :: Expr
nat = EData "nat" natRec

zero = (EVar "Z")
one = EApp (EVar "S") [zero]

-- Nat Stream

natStreamBody :: [(Sym, Type)]
natStreamBody = [
                  ("head", TGlobTypeVar "nat"),
                  ("tail", TRecTypeVar "natStream")
                ]

natStreamRec :: Type
natStreamRec = TRecCoind "natStream" natStreamBody

natStream :: Expr
natStream = ECodata "natStream" natStreamRec

-- List of natural numbers

natListBody :: Type
natListBody = TVari [
                ("nil", []),
                ("cons", [(TGlobTypeVar "nat"), (TRecTypeVar "natList")])
              ]
natListRec :: Type              
natListRec = TRecInd "natList" natListBody

natList :: Expr
natList = EData "natList" natListRec

emptyList = (EVar "nil")


-- Functions on natural numbers

subtractSlowly, subtractSlowlyBody :: Expr
-- let subtractSlowly n =
--   case n of
--     Z    -> Z
--     S n' -> n' 
subtractSlowly = EGlobLet "subtractSlowly" (TArr [TGlobTypeVar "nat"] (TGlobTypeVar "nat")) (Just [("n", TGlobTypeVar "nat")]) subtractSlowlyBody
subtractSlowlyBody =
  ECase (EApp (EUnfold (TGlobTypeVar "nat")) [(EVar "n")]) [
    ("Z", ([], EApp (EFold (TGlobTypeVar "nat")) [(ETag "Z" [] natBody)])),
    ("S", (["n'"], (EApp (EVar "subtractSlowly") [(EVar "n'")])))
  ]

subtractSlowlyWithPred, subtractSlowlyWithPredBody :: Expr
-- let subtractSlowlyWithPred n =
--   let pred m =
--     case m of
--       Z -> Z
--       S m' -> m'
--   in case n of
--        Z -> Z
--        S n' -> subtractSlowlyWithPred (pred n)
subtractSlowlyWithPred = EGlobLet "subtractSlowlyWithPred" (TArr [TGlobTypeVar "nat"] (TGlobTypeVar "nat")) (Just [("n", TGlobTypeVar "nat")]) subtractSlowlyWithPredBody
subtractSlowlyWithPredBody =
  ELet "pred" (TArr [TGlobTypeVar "nat"] (TGlobTypeVar "nat")) (Just [("m", TGlobTypeVar "nat")])
    (ECase (EApp (EUnfold (TGlobTypeVar "nat")) [EVar "m"]) [
      ("Z", ([], EVar "Z")),
      ("S", (["m'"], EVar "m'"))
    ])
    (ECase (EApp (EUnfold (TGlobTypeVar "nat")) [EVar "n"]) [
      ("Z", ([], EVar "Z")),
      ("S", (["n'"], EApp (EVar "subtractSlowlyWithPred") [(EApp (EVar "pred") [EVar "n"])]))
    ])

forever, foreverBody :: Expr
-- let forever x = forever x
forever = EGlobLet "forever" (TArr [TGlobTypeVar "nat"] (TGlobTypeVar "nat")) (Just [("x", TGlobTypeVar "nat")]) foreverBody
foreverBody = EApp (EVar "forever") [(EVar "x")]

-- Third example from original size-change paper
scEx3, scEx3Body :: Expr
-- let scEx3 m n =
--   case m of
--     Z -> S n
--     S m' -> case n of
--               Z -> scEx3 m' 1
--               S n' -> scEx3 m' (scEx3 m n') 
scEx3 = EGlobLet "scEx3" (TArr [TGlobTypeVar "nat", TGlobTypeVar "nat"] (TGlobTypeVar "nat")) (Just [("m", TGlobTypeVar "nat"), ("n", TGlobTypeVar "nat")]) scEx3Body
scEx3Body =
  ECase (EApp (EUnfold (TGlobTypeVar "nat")) [(EVar "m")]) [
    ("Z", ([], EApp (EVar "S") [(EVar "n")])),
    ("S", (["m'"], (ECase (EApp (EUnfold (TGlobTypeVar "nat")) [(EVar "n")]) [
                       ("Z", ([], EApp (EVar "scEx3") [(EVar "m'"), one])),
                       ("S", (["n'"], EApp (EVar "scEx3") [(EVar "m'"), (EApp (EVar "scEx3") [(EVar "m"), (EVar "n'")])]))
    ])))
  ]

-- Fourth example from original size-change paper
scEx4, scEx4Body :: Expr
-- let scEx4 m n r =
--   case r of
--     Z -> case n of
--            Z -> m
--            S n' -> scEx4 r n' m
--     S r' -> scEx4 m r' n
scEx4 = EGlobLet "scEx4" (TArr [TGlobTypeVar "nat", TGlobTypeVar "nat", TGlobTypeVar "nat"] (TGlobTypeVar "nat")) 
        (Just [("m", TGlobTypeVar "nat"), ("n", TGlobTypeVar "nat"), ("r", TGlobTypeVar "nat")]) scEx4Body
scEx4Body =
  ECase (EApp (EUnfold (TGlobTypeVar "nat")) [(EVar "r")]) [
    ("Z", ([], ECase (EApp (EUnfold (TGlobTypeVar "nat")) [(EVar "n")]) [
                 ("Z", ([], EVar "m")),
                 ("S", (["n'"], EApp (EVar "scEx4") [(EVar "r"), (EVar "n'"), (EVar "m")]))
     ])),
    ("S", (["r'"], EApp (EVar "scEx4") [(EVar "m"), (EVar "r'"), (EVar "n")]))
  ]


-- Functions on lists of natural numbers

-- First example from the original size-change paper (reverse)
scEx1, scEx1Body :: Expr
-- let scEx1 ls =
--  let r1 ls a =
--    case ls of
--      nil         -> a
--      (cons x xs) -> r1 xs (cons x a)
--  in r1 ls nil
scEx1 = EGlobLet "scEx1" (TArr [TGlobTypeVar "natList"] (TGlobTypeVar "natList")) (Just [("ls", TGlobTypeVar "natList")]) scEx1Body
scEx1Body =
  ELet "r1" (TArr [TGlobTypeVar "natList", TGlobTypeVar "natList"] (TGlobTypeVar "natList")) (Just [("ls", TGlobTypeVar "natList"), ("a", TGlobTypeVar "natList")])
    (ECase (EApp (EUnfold (TGlobTypeVar "natList")) [(EVar "ls")]) [
        ("nil", ([], EVar "a")),
        ("cons", (["x", "xs"], EApp (EVar "r1") [(EVar "xs"), (EApp (EVar "cons") [(EVar "x"), (EVar "a")])]))
    ])
    (EApp (EVar "r1") [(EVar "ls"), emptyList])
