module TypeChecker where

import Data.Either
import Control.Monad.Error
import Control.Monad.Identity
import Findus

fib 0 = 0
fib 1 = 1
fib n = fib(n-1) + fib(n-2)

fibs' = 0 : 1 : zipWith (+) fibs' (tail fibs')

fibs n = fibs' !! n

data TypedExpr
  = TEUnit       Type
  | TEVar        Type Sym
  | TELam        Type Sym Type TypedExpr
  | TEApp        Type TypedExpr TypedExpr
  | TELit        Type Lit
  | TELet        Type Sym TypedExpr TypedExpr
  | TEIf         Type TypedExpr TypedExpr TypedExpr
  | TETuple      Type [TypedExpr]
  | TETupProj    Type TypedExpr TypedExpr
  | TERecord     Type [(Sym, TypedExpr)]
  | TERecordProj Type TypedExpr Sym
  | TECase       Type TypedExpr [(Sym, (Sym, TypedExpr))]
  | TETag        Type Sym TypedExpr
  | TEFold       Type Type
  | TEUnfold     Type Type
  | TEData       Type Sym
  | TELetFun     Type Sym TypedExpr
  deriving (Eq, Show)

getTypeAnno :: TypedExpr -> Type
getTypeAnno (TEUnit       t      ) = t
getTypeAnno (TEVar        t _    ) = t
getTypeAnno (TELam        t _ _ _) = t
getTypeAnno (TEApp        t _ _  ) = t
getTypeAnno (TELit        t _    ) = t
getTypeAnno (TELet        t _ _ _) = t
getTypeAnno (TEIf         t _ _ _) = t
getTypeAnno (TETuple      t _    ) = t
getTypeAnno (TETupProj    t _ _  ) = t
getTypeAnno (TERecord     t _    ) = t
getTypeAnno (TERecordProj t _ _  ) = t
getTypeAnno (TECase       t _ _  ) = t
getTypeAnno (TETag        t _ _  ) = t
getTypeAnno (TEFold       t _    ) = t
getTypeAnno (TEUnfold     t _    ) = t
getTypeAnno (TEData       t _    ) = t
getTypeAnno (TELetFun     t _ _  ) = t

data TypeError = Err String deriving Show

instance Error TypeError where
  noMsg = Err ""

typeEquality :: Type -> Type -> Either TypeError Type
typeEquality t1 t2 | t1 == t2  = return t1
                   | otherwise = throwError $ Err ("Type mismatch: " ++ (shows t1 "") ++ " is not a " ++ (shows t2 ""))

check :: Env -> Env -> Expr -> Either TypeError TypedExpr
check _ _ EUnit              = return $ TEUnit TUnit

check _ _ (ELit (LInt i))    = return $ TELit TInt (LInt i)
check _ _ (ELit (LBool b))   = return $ TELit TBool (LBool b)
check _ _ (ELit (LString s)) = return $ TELit TString (LString s)

check vEnv tEnv (EVar x) = case (lookup x vEnv) of
	Just e  -> return $ TEVar e x
	Nothing -> throwError $ Err (x ++ " not in scope")
check vEnv tEnv (ELam x t e) = do
  rhs <- (check ((x,t) : vEnv) tEnv e)
  return $ TELam (TArr t (getTypeAnno rhs)) x t rhs 
check vEnv tEnv (EApp e1 e2) = do
  te1 <- check vEnv tEnv e1
  te2 <- check vEnv tEnv e2
  case getTypeAnno te1 of
    (TArr f a) -> case typeEquality f (getTypeAnno te2) of
                    Right _ -> return $ TEApp a te1 te2
                    Left x  -> throwError x
    _ -> throwError $ Err "Application on non arrow type"
check vEnv tEnv (ELet x e1 e2) = do
  te1 <- check vEnv tEnv e1
  te2 <- check ((x, (getTypeAnno te1)) : vEnv) tEnv e2
  return $ TELet (getTypeAnno te2) x te1 te2
check vEnv tEnv (EIf c b1 b2) = do
  ct <- check vEnv tEnv c
  case getTypeAnno ct of  
    TBool -> do
      te1 <- check vEnv tEnv b1
      te2 <- check vEnv tEnv b2
      case (typeEquality (getTypeAnno te1) (getTypeAnno te2)) of
        Right(t) -> return $ TEIf t ct te1 te2
        _        -> throwError $ Err "Types of branches in IF are not equal"
    _ -> throwError $ Err "Conditional of IF not a Boolean type"
check vEnv tEnv (ETuple es) = do
  let ts = map (check vEnv tEnv) es in
    case lefts ts of
      []    -> return $ TETuple (TTuple (map getTypeAnno (rights ts))) (rights ts)
      x : _ -> throwError x
check vEnv tEnv (ETupProj e l) = do
  te <- check vEnv tEnv e
  case l of
    ELit li ->
      case li of
        LInt i ->
          case getTypeAnno te of
            TTuple ts | length ts > i -> return $ TETupProj (ts !! i) te (TELit TInt li)
            TTuple ts                 -> throwError $ Err "Tuple index too large"
            _                         -> throwError $ Err "Tuple projection attempted on non tuple type"
        _ -> throwError $ Err "Tuple index not an integer"
    _ -> throwError $ Err "Tuple index not a literate"
check vEnv tEnv (ERecord es) = do
  let ts = map (check vEnv tEnv) (map snd es) in
    case lefts ts of
      []    -> return $ TERecord (TRecord (zip (map fst es) (map getTypeAnno (rights ts)))) (zip (map fst es) (rights ts))
      x : _ -> throwError x
check vEnv tEnv (ERecordProj e s) = do
  case e of
    ERecord es ->
      case lookup s es of
        Just exp -> do
          texp <- check vEnv tEnv exp
          return $ TERecordProj (getTypeAnno texp) texp s
        Nothing  -> throwError $ Err (s ++ "not in record scope")
    _       -> throwError $ Err "Record projection on non record"
check vEnv tEnv (ETag s e t) = do
  case t of
    TVari fs ->
      case lookup s fs of
        Just et -> do
          te <- check vEnv tEnv e
          case typeEquality (getTypeAnno te) et of
            Right _ -> return $ TETag t s te
            Left  x -> throwError x
        Nothing -> throwError $ Err "Label not found in variant type"
    _ -> throwError $ Err "Can only tag as variant types"
check vEnv tEnv (ECase e es) = do
  te <- check vEnv tEnv e
  case getTypeAnno te of
    (TRec s vt) ->
      case vt of
        TVari fs ->
          if (not $ all (\x -> elem x (map fst fs)) (map fst es)) 
            then throwError $ Err "Not all case labels were in type" 
            else 
              let vEnvs = map (: vEnv) (zip (map fst (map snd es)) (map snd fs)) in
                let ts = zipWith (\v e -> check v tEnv e) vEnvs (map snd (map snd es)) in
                  case lefts ts of
                    []    -> 
                      case rights ts of
                        [] -> throwError $ Err "No cases"
                        t : ts -> 
                          case lefts $ map (typeEquality (getTypeAnno t)) (map getTypeAnno ts) of
                            [] -> return $ TECase (getTypeAnno t) te (zip (map fst es) (zip (map fst (map snd es)) (t : ts)))
                            x : _ -> throwError x
                    x : _ -> throwError x
        _ -> throwError $ Err "Not a variant type"
    _ -> throwError $ Err "Expected recursive type in case"
check vEnv tEnv (EFold t) = do
  case t of
    TRec s nt -> return $ TEFold (TArr nt t) t
    _         -> throwError $ Err "Fold attempted on non recursive type"
check vEnv tEnv (EUnfold t) = do
  case t of
    TRec s nt -> return $ TEUnfold (TArr t (TRec s (substTypeVari s t nt))) t
    _         -> throwError $ Err "Unfold attempted on non recursive type"
check vEnv tEnv (EData s t) = 
  case t of
    TRec s' nt | s == s' -> return $ TEData (TRec s nt) s
               | otherwise -> throwError $ Err "Data labels not matching"
    _                      -> throwError $ Err "Not a recursive types"
check vEnv tEnv (ELetFun s t e) = do
  te <- check vEnv tEnv e
  case typeEquality (getTypeAnno te) t of
    Right _ -> return $ TELetFun t s te
    Left _  -> throwError $ Err ("Annotated type does not match actual type of function " ++ s)
check _ _ _ = throwError $ Err "Not a valid expression"

checkSym :: Env -> Sym -> Either TypeError Type
checkSym []            name = throwError $ Err (name ++ " not found")
checkSym ((l, t) : es) name | l == name = return t
                            | otherwise = checkSym es name

substTypeVari :: Sym -> Type -> Type -> Type
substTypeVari s t (TArr  t1 t2) = TArr    (substTypeVari s t t1) (substTypeVari s t t2)
substTypeVari s t (TTuple   ts) = TTuple  (map (substTypeVari s t) ts)
substTypeVari s t (TRecord  ts) = TRecord $ zip (fst $ unzip ts) (map (substTypeVari s t) (snd $ unzip ts))
substTypeVari s t (TVari    ts) = TVari   $ zip (fst $ unzip ts) (map (substTypeVari s t) (snd $ unzip ts))
substTypeVari s t (TRec  s' t') = TRec    s' (substTypeVari s t t')
substTypeVari s t (TTypeVar s') | s == s' = t
substTypeVari _ _ a = a

buildRootEnv :: [Expr] -> Either TypeError (Env, Env)
buildRootEnv []       = Right ([], [])
buildRootEnv (x : xs) = case buildRootEnv xs of
                          Right l -> 
                            case x of
                              EData   s t   -> return $ (fst l, (s, t) : (snd l))
                              ELetFun s t _ -> return $ ((s, t) : (fst l), snd l)
                              _             -> throwError $ Err "Not a valid root type"
                          Left  e -> throwError e

checkRoot :: Expr -> Either TypeError [TypedExpr]
checkRoot (ERoot es) = case buildRootEnv es of
                         Right l -> 
                          let ts = map (check (fst l) (snd l)) es in 
                            case lefts $ ts of
                              []    -> return $ rights ts
                              e : _ -> throwError e
                         Left  e -> throwError e

