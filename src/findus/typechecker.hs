module TypeChecker where

import Prelude
import Data.Either
import Control.Monad.Error
import Control.Monad.Identity
import Findus

data TypeError = Err String deriving Show

instance Error TypeError where
  noMsg = Err ""

typeEquality :: Type -> Type -> Either TypeError Type
typeEquality t1 t2 | t1 == t2 = Right t1
typeEquality t1 t2            = throwError $ Err ("Type mismatch: " ++ (shows t1 "") ++ " is not a " ++ (shows t2 ""))

check :: Env -> Env -> Expr -> Either TypeError Type
check _ _ EUnit              = return TUnit
check _ _ (ELit (LInt _))    = return TInt
check _ _ (ELit (LBool _))   = return TBool
check _ _ (ELit (LString _)) = return TString
check vEnv tEnv (EVar x) = case (lookup x vEnv) of
	Just e  -> return e
	Nothing -> throwError $ Err (x ++ " not in scope")
check vEnv tEnv (ELam x t e) = do
	rhs <- (check ((x,t) : vEnv) tEnv e)
	return (TArr t rhs)
check vEnv tEnv (EApp e1 e2) = do
	t1 <- check vEnv tEnv e1
	t2 <- check vEnv tEnv e2
	case t1 of
		(TArr f a) -> case typeEquality f t2 of
                    Right _ -> return a
                    Left x  -> throwError x
		_ -> throwError $ Err "Not an arrow type"
check vEnv tEnv (ELet x e1 e2) = do
  t1 <- check vEnv tEnv e1
  t2 <- check ((x, t1) : vEnv) tEnv e2
  return t2
check vEnv tEnv (EIf c b1 b2) = do
  ct <- check vEnv tEnv c
  bt <- typeEquality ct TBool
  t1 <- check vEnv tEnv b1
  t2 <- check vEnv tEnv b2
  (typeEquality t1 t2)
check vEnv tEnv (EPair e1 e2) = do
  t1 <- check vEnv tEnv e1
  t2 <- check vEnv tEnv e2
  return (TProd t1 t2)
check vEnv tEnv (EFst e) = do
  t <- check vEnv tEnv e
  case t of
    (TProd t1 _) -> return t1
    _            -> throwError $ Err "Not a product type"
check vEnv tEnv (ESnd e) = do
  t <- check vEnv tEnv e
  case t of
    (TProd _ t2) -> return t2
    _            -> throwError $ Err "Not a product type"
check vEnv tEnv (ETuple es) = do
  let ts = map (check vEnv tEnv) es in
    case lefts ts of
      []    -> return (TTuple (rights ts))
      x : _ -> throwError x
check vEnv tEnv (ETupProj e l) = do
  t <- check vEnv tEnv e
  case l of
    ELit li ->
      case li of
        LInt i ->
          case t of
            TTuple ts | length ts > i -> return $ ts !! i
            TTuple ts                 -> throwError $ Err "Too large an index"
            _                         -> throwError $ Err "Not a tuple type"
        _ -> throwError $ Err "Index not an integer"
    _ -> throwError $ Err "Index not a literate"
check vEnv tEnv (ERecord es) = do
  let ts = map (check vEnv tEnv) (map snd es) in
    case lefts ts of
      []    -> return (TRecord (zip (map fst es) (rights ts)))
      x : _ -> throwError x
check vEnv tEnv (ERecordProj e s) = do
  case e of
    ERecord es ->
      case lookup s es of
        Just exp -> check vEnv tEnv exp
        Nothing  -> throwError $ Err "Not in scope"
    _       -> throwError $ Err "Not a record"
check vEnv tEnv (ETag s e t) = do
  case t of
    TVari fs ->
      case lookup s fs of
        Just et -> do
          at <- check vEnv tEnv e
          case typeEquality at et of
            Right _ -> return t
            Left  x -> throwError x
        Nothing -> throwError $ Err "Label not found in variant type"
    _ -> throwError $ Err "Not a variant type"
check vEnv tEnv (ECase e es) = do
  (TRec s vt) <- check vEnv tEnv e
  case vt of
    TVari fs ->
      if (not $ all (\x -> elem x (map fst fs)) (map fst es)) 
        then throwError $ Err "Not all labels were in type" 
        else 
          let vEnvs = map (: vEnv) (zip (map fst (map snd es)) (map snd fs)) in
            let ts = zipWith (\v e -> check v tEnv e) vEnvs (map snd (map snd es)) in
              case lefts ts of
                []    -> 
                  case rights ts of
                    [] -> throwError $ Err "No cases"
                    t : ts -> 
                      case lefts $ map (typeEquality t) ts of
                        [] -> return t
                        x : _ -> throwError x
                x : _ -> throwError x
    _ -> throwError $ Err "Not a variant type"
check vEnv tEnv (EFix e) = do
  t <- check vEnv tEnv e
  case t of
    TArr i o -> typeEquality i o
    _ -> throwError $ Err "Not an arrow type"
check vEnv tEnv (EFold t) = do
  case t of
    TRec s nt -> return $ TArr nt t
    _         -> throwError $ Err "Not a recursive type"
check vEnv tEnv (EUnfold t) = do
  case t of
    TRec s nt -> return $ TArr t (TRec s (substTypeVari s t nt))
    _         -> throwError $ Err "Not a recursive type"
check vEnv tEnv (EData s t) = 
  case t of
    TRec s' nt | s == s' -> return $ TRec s nt
               | otherwise -> throwError $ Err "Data labels not matching"
    _                      -> throwError $ Err "Not a recursive type"
check vEnv tEnv (ELetFun s t e) = do
  at <- check vEnv tEnv e
  typeEquality at t
check _ _ _ = throwError $ Err "Not a valid expression"

checkSym :: Env -> Sym -> Either TypeError Type
checkSym []            name = throwError $ Err (name ++ " not found")
checkSym ((l, t) : es) name | l == name = return t
                            | otherwise = checkSym es name

substRecType :: Sym -> Type -> Type
substRecType s (TArr  t1 t2) = TArr  (substRecType s t1) (substRecType s t2)
substRecType s (TProd t1 t2) = TProd (substRecType s t1) (substRecType s t2)
substRecType s (TTuple   ts) = TTuple $ map (substRecType s) ts
substRecType s (TRecord  ts) = TRecord $ zip (fst $ unzip ts) (map (substRecType s) (snd $ unzip ts))
substRecType s (TVari    ts) = TVari   $ zip (fst $ unzip ts) (map (substRecType s) (snd $ unzip ts))
substRecType s (TRec  s'  t) | s == s'   = TTypeVar s
                             | otherwise = TRec s' (substRecType s t)
substRecType _ a = a

findTypeVars :: Type -> [Sym] -> [Sym]
findTypeVars (TArr  t1 t2) ss = findTypeVars t1 ss ++ findTypeVars t2 ss
findTypeVars (TProd t1 t2) ss = findTypeVars t1 ss ++ findTypeVars t2 ss
findTypeVars (TTuple   ts) ss = concat $ map (\x -> findTypeVars x ss) ts
findTypeVars (TRecord  ts) ss = concat $ map (\x -> findTypeVars x ss) (snd $ unzip ts)
findTypeVars (TVari    ts) ss = concat $ map (\x -> findTypeVars x ss) (snd $ unzip ts)
findTypeVars (TRec  s   t) ss = findTypeVars t (s : ss)
findTypeVars (TTypeVar  s) ss = if elem s ss then [] else [s]
findTypeVars _ _ = []

substTypeVari :: Sym -> Type -> Type -> Type
substTypeVari s t (TArr  t1 t2) = TArr    (substTypeVari s t t1) (substTypeVari s t t2)
substTypeVari s t (TProd t1 t2) = TProd   (substTypeVari s t t1) (substTypeVari s t t2)
substTypeVari s t (TTuple   ts) = TTuple  (map (substTypeVari s t) ts)
substTypeVari s t (TRecord  ts) = TRecord $ zip (fst $ unzip ts) (map (substTypeVari s t) (snd $ unzip ts))
substTypeVari s t (TVari    ts) = TVari   $ zip (fst $ unzip ts) (map (substTypeVari s t) (snd $ unzip ts))
substTypeVari s t (TRec  s' t') = TRec    s' (substTypeVari s t t')
substTypeVari s t (TTypeVar s') | s == s' = t
substTypeVari _ _ a = a

checkExpr :: Expr -> Either TypeError Type
checkExpr x = check [] [] x

buildRootEnv :: [Expr] -> Either TypeError (Env, Env)
buildRootEnv []       = Right ([], [])
buildRootEnv (x : xs) = case buildRootEnv xs of
                          Right l -> 
                            case x of
                              EData   s t   -> return $ (fst l, (s, t) : (snd l))
                              ELetFun s t _ -> return $ ((s, t) : (fst l), snd l)
                              _             -> throwError $ Err "Not a valid root type"
                          Left  e -> throwError e

                        

checkRoot :: Expr -> Either TypeError [Type]
checkRoot (ERoot es) = case buildRootEnv es of
                         Right l -> 
                          let ts = map (check (fst l) (snd l)) es in 
                            case lefts $ ts of
                              []    -> return $ rights ts
                              e : _ -> throwError e
                         Left  e -> throwError e

