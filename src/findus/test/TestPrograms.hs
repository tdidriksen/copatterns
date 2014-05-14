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

-- Third example from original size-change paper (negative test)
scEx3neg, scEx3negBody :: Expr
-- let scEx3neg m n =
--   case m of
--     Z -> S n
--     S m' -> case n of
--               Z -> scEx3neg m' 1
--               S n' -> scEx3neg m' (scEx3neg m n') 
scEx3neg = EGlobLet "scEx3neg" (TArr [TGlobTypeVar "nat", TGlobTypeVar "nat"] (TGlobTypeVar "nat")) (Just [("m", TGlobTypeVar "nat"), ("n", TGlobTypeVar "nat")]) scEx3negBody
scEx3negBody =
  ECase (EApp (EUnfold (TGlobTypeVar "nat")) [(EVar "m")]) [
    ("Z", ([], EApp (EVar "S") [(EVar "n")])),
    ("S", (["m'"], (ECase (EApp (EUnfold (TGlobTypeVar "nat")) [(EVar "n")]) [
                       ("Z", ([], EApp (EVar "scEx3neg") [(EVar "m'"), one])),
                       ("S", (["n'"], EApp (EVar "scEx3neg") [(EVar "m'"), (EApp (EVar "scEx3neg") [(EVar "m"), (EVar "n")])]))
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

-- Fourth example from original size-change paper (negative test)
scEx4neg, scEx4negBody :: Expr
-- let scEx4neg m n r =
--   case r of
--     Z -> case n of
--            Z -> m
--            S n' -> scEx4neg r n' m
--     S r' -> scEx4neg m r' n
scEx4neg = EGlobLet "scEx4neg" (TArr [TGlobTypeVar "nat", TGlobTypeVar "nat", TGlobTypeVar "nat"] (TGlobTypeVar "nat")) 
        (Just [("m", TGlobTypeVar "nat"), ("n", TGlobTypeVar "nat"), ("r", TGlobTypeVar "nat")]) scEx4negBody
scEx4negBody =
  ECase (EApp (EUnfold (TGlobTypeVar "nat")) [(EVar "r")]) [
    ("Z", ([], ECase (EApp (EUnfold (TGlobTypeVar "nat")) [(EVar "n")]) [
                 ("Z", ([], EVar "m")),
                 ("S", (["n'"], EApp (EVar "scEx4neg") [(EVar "r"), (EVar "n'"), (EVar "m")]))
     ])),
    ("S", (["r'"], EApp (EVar "scEx4neg") [(EVar "m"), (EVar "r"), (EVar "n")]))
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


-- Second example from original size-change paper
-- let scEx2f i x =
--  case i of
--    nil -> x
--    cons hd tl -> scEx2g tl x i
scEx2f = EGlobLet "scEx2f" (TArr [TGlobTypeVar "natList", TGlobTypeVar "nat"] (TGlobTypeVar "nat")) (Just [("i", TGlobTypeVar "natList"), ("x", TGlobTypeVar "nat")]) scEx2fBody
scEx2fBody =
  (ECase (EApp (EUnfold (TGlobTypeVar "natList")) [(EVar "i")]) [
    ("nil", ([], EVar "x")),
    ("cons", (["hd", "tl"], EApp (EVar "scEx2g") [(EVar "tl"), (EVar "x"), (EVar "i")]))
   ])

-- let scEx2g a b c =
--   f a (cons b c)
scEx2g = EGlobLet "scEx2g" (TArr [TGlobTypeVar "natList", TGlobTypeVar "nat", TGlobTypeVar "natList"] (TGlobTypeVar "nat")) (Just [("a", TGlobTypeVar "natList"), ("b", TGlobTypeVar "nat"), ("c", TGlobTypeVar "natList")]) scEx2gBody
scEx2gBody =
  EApp (EVar "scEx2f") [(EVar "a"), (EApp (EVar "S") [EVar "b"])]


-- Fifth example from original size-change paper
-- let scEx5 x y =
--  case y of
--    nil -> x
--    cons yhd ytl ->
--      case x of
--        nil -> scEx5 y ytl
--        cons xhd xtl -> scEx5 y xtl
scEx5 = EGlobLet "scEx5" (TArr [TGlobTypeVar "natList", TGlobTypeVar "natList"] (TGlobTypeVar "natList")) (Just [("x", TGlobTypeVar "natList"), ("y", TGlobTypeVar "natList")]) scEx5Body
scEx5Body =
  (ECase (EApp (EUnfold (TGlobTypeVar "natList")) [(EVar "y")]) [
    ("nil", ([], EVar "x")),
    ("cons", (["yhd", "ytl"],
        (ECase (EApp (EUnfold (TGlobTypeVar "natList")) [(EVar "x")]) [
            ("nil", ([], EApp (EVar "scEx5") [(EVar "y"), (EVar "ytl")])),
            ("cons", (["xhd", "xtl"], EApp (EVar "scEx5") [(EVar "y"), (EVar "xtl")]))
        ])
      ))
   ])


-- Sixth example from original size-change paper
-- let scEx6f a b =
--  case b of
--    nil -> scEx6g a nil
--    cons bhd btl -> scEx6f (cons bhd a) btl
scEx6f = EGlobLet "scEx6f" (TArr [TGlobTypeVar "natList", TGlobTypeVar "natList"] (TGlobTypeVar "natList")) (Just [("a", TGlobTypeVar "natList"), ("b", TGlobTypeVar "natList")]) scEx6fBody
scEx6fBody =
  (ECase (EApp (EUnfold (TGlobTypeVar "natList")) [(EVar "b")]) [
    ("nil", ([], EApp (EVar "scEx6g") [(EVar "a"), emptyList])),
    ("cons", (["bhd", "btl"], EApp (EVar "scEx6f") [(EApp (EVar "cons") [EVar "bhd", EVar "a"]), (EVar "btl")]))
   ])

-- let scEx6g c d =
--   case c of
--     nil -> d
--     cons chd ctl -> scEx6g ctl (cons chd d)
scEx6g = EGlobLet "scEx6g" (TArr [TGlobTypeVar "natList", TGlobTypeVar "natList"] (TGlobTypeVar "natList")) (Just [("c", TGlobTypeVar "natList"), ("d", TGlobTypeVar "natList")]) scEx6gBody
scEx6gBody =
  (ECase (EApp (EUnfold (TGlobTypeVar "natList")) [(EVar "c")]) [
    ("nil", ([], EVar "d")),
    ("cons", (["chd", "ctl"], EApp (EVar "scEx6g") [(EVar "ctl"), (EApp (EVar "cons") [EVar "chd", EVar "d"])]))
  ])

