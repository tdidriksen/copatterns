module TestPrograms where

import Expr

-- Natural numbers

natBody :: Type
natBody = TVari [
            ("Z", []), 
            ("S", [TRecTypeVar "nat"])
          ]
natRec :: Type
natRec = TRecInd "nat" (natBody)

nat :: Expr
nat = EData "nat" natRec


-- Functions on natural numbers

subtractSlowly, subtractSlowlyBody :: Expr
subtractSlowly = EGlobLet "subtractSlowly" (TArr [TGlobTypeVar "nat"] (TGlobTypeVar "nat")) (Just [("n", TGlobTypeVar "nat")]) subtractSlowlyBody
subtractSlowlyBody =
  ECase (EApp (EUnfold (TGlobTypeVar "nat")) [(EVar "n")]) [
    ("Z", ([], EApp (EFold (TGlobTypeVar "nat")) [(ETag "Z" [] natBody)])),
    ("S", (["n'"], (EApp (EVar "subtractSlowly") [(EVar "n'")])))
  ]
