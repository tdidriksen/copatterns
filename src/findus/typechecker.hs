{-# LANGUAGE FlexibleInstances #-}

module TypeChecker where

import Data.Either
import Control.Monad.Error
import Control.Monad.Identity
import Findus
import Data.Graph.Inductive.Query.Monad

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
  | TECase       Type TypedExpr [(Sym, ([Sym], TypedExpr))]
  | TETag        Type Sym [TypedExpr]
  | TEFold       Type Type
  | TEUnfold     Type Type
  | TEData       Type Sym
  | TELetFun     Type Sym TypedExpr
  | TELetRec     Type Sym TypedExpr TypedExpr
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
getTypeAnno (TELetRec     t _ _ _) = t

data TypeError = Err String deriving Show

instance Error TypeError where
  noMsg = Err ""

typeVarLookup :: Sym -> Env -> Either TypeError Type
typeVarLookup s env = case lookup s env of
                       Just(t) -> return t
                       Nothing -> throwError $ Err ("Data Type " ++ s  ++ " not found") 

typeEquality :: Type -> Type -> Env -> Either TypeError Type
typeEquality t1 t2 env | t1 == t2 = return t1
                       | otherwise = case (t1, t2) of
                          (TGlobTypeVar s, t2) -> do
                              t1 <- typeVarLookup s env
                              typeEquality t1 t2 env
                          (t1, TGlobTypeVar s) -> do
                              t2 <- typeVarLookup s env
                              typeEquality t1 t2 env
                          (_, _) -> throwError $ Err ("Type mismatch: " ++ (show t1 ) ++ " is not a " ++ (show t2))

listTypeEquality :: [Type] -> [Type] -> Env -> Either TypeError [Type]
listTypeEquality (x : xs) (y : ys) env = do
  t <- (typeEquality x y env)
  ts <- (listTypeEquality xs ys env)
  return $ t : ts
listTypeEquality [] [] env = return []
listTypeEquality _ _ env = throwError $ Err "Type mismatch"

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
    (TArr f a) -> case typeEquality f (getTypeAnno te2) tEnv of
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
      case (typeEquality (getTypeAnno te1) (getTypeAnno te2)) tEnv of
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
          let te = map (check vEnv tEnv) e in
            case lefts te of
              []     ->
                case listTypeEquality (map getTypeAnno (rights te)) et tEnv of
                  Right _ -> return $ TETag t s (rights te)
                  Left  x -> throwError x
              x : _  -> throwError x
        Nothing -> throwError $ Err "Label not found in variant type"
    TGlobTypeVar s       -> do
                          t <- typeVarLookup s tEnv
                          check vEnv tEnv (ETag s e t)
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
              let vEnvs = map (: vEnv) (zip (concat (map fst (map snd es))) (concat (map snd fs))) in
                let ts = zipWith (\v e -> check v tEnv e) vEnvs (map snd (map snd es)) in
                  case lefts ts of
                    []    -> 
                      case rights ts of
                        [] -> throwError $ Err "No cases"
                        t : ts -> 
                          case lefts $ map (\t2 -> typeEquality (getTypeAnno t) t2 tEnv) (map getTypeAnno ts) of
                            [] -> return $ TECase (getTypeAnno t) te (zip (map fst es) (zip (map fst (map snd es)) (t : ts)))
                            x : _ -> throwError x
                    x : _ -> throwError x
        _ -> throwError $ Err "Not a variant type"
    _ -> throwError $ Err "Expected recursive type in case"
check vEnv tEnv (EFold t) = do
  case t of
    TRec s nt -> return $ TEFold (TArr nt t) t
    TGlobTypeVar s -> do
                  t <- typeVarLookup s tEnv
                  check vEnv tEnv (EFold t)
    _         -> throwError $ Err "Fold attempted on non recursive type"
check vEnv tEnv (EUnfold t) = do
  case t of
    TRec s nt -> return $ TEUnfold (TArr t (TRec s (substTypeVari s t nt))) t
    TGlobTypeVar s       -> do
                          t <- typeVarLookup s tEnv
                          check vEnv tEnv (EUnfold t)
    _         -> throwError $ Err ("Unfold attempted on non recursive type: " ++ (show t))
check vEnv tEnv (EData s t) = 
  case t of
    TRec s' nt | s == s' -> return $ TEData (TRec s nt) s
               | otherwise -> throwError $ Err "Data labels not matching"
    TGlobTypeVar s       -> do
                          t <- typeVarLookup s tEnv
                          check vEnv tEnv (EData s t)
    _                    -> throwError $ Err "Not a recursive types"
check vEnv tEnv (ELetFun s t e) = do
  te <- check vEnv tEnv e
  case typeEquality (getTypeAnno te) t tEnv of
    Right _ -> return $ TELetFun t s te
    Left _  -> throwError $ Err ("Annotated type " ++ (show t) ++ " does not match actual type " ++ (show $ getTypeAnno te) ++ " of function " ++ s)
check vEnv tEnv (ELetRec x t e1 e2) = do
  te1 <- check ((x, t) : vEnv) tEnv e1
  te2 <- check ((x, t) : vEnv) tEnv e2
  case typeEquality t (getTypeAnno te1) tEnv of
    Right(_) -> return $ TELetRec (getTypeAnno te2) x te1 te2
    Left(e) -> throwError e
check _ _ _ = throwError $ Err "Not a valid expression"

listMapFst :: (a -> c) -> [(a, b)] -> [(c, b)]
listMapFst f p = zip (map f (fst $ unzip p)) (snd $ unzip p)

listMapSnd :: (b -> c) -> [(a, b)] -> [(a, c)]
listMapSnd f p = zip (fst $ unzip p) (map f (snd $ unzip p))

checkSym :: Env -> Sym -> Either TypeError Type
checkSym []            name = throwError $ Err (name ++ " not found")
checkSym ((l, t) : es) name | l == name = return t
                            | otherwise = checkSym es name

substTypeVari :: Sym -> Type -> Type -> Type
substTypeVari s t (TArr  t1 t2) = TArr    (substTypeVari s t t1) (substTypeVari s t t2)
substTypeVari s t (TTuple   ts) = TTuple  (map (substTypeVari s t) ts)
substTypeVari s t (TRecord  ts) = TRecord $ listMapSnd (substTypeVari s t) ts
substTypeVari s t (TVari    ts) = TVari   $ listMapSnd (map $ substTypeVari s t) ts
substTypeVari s t (TRec  s' t') = TRec    s' (substTypeVari s t t')
substTypeVari s t (TRecTypeVar s') | s == s' = t
substTypeVari _ _ a = a


globTypeSubst :: Env -> Type -> Type
globTypeSubst env (TArr t1 t2)     = TArr (globTypeSubst env t1) (globTypeSubst env t2)
globTypeSubst env (TTuple ts)      = TTuple (map (globTypeSubst env) ts)
globTypeSubst env (TRecord ts)     = TRecord $ listMapSnd (globTypeSubst env) ts
globTypeSubst env (TVari ts)       = TVari $ listMapSnd (map $ globTypeSubst env) ts
globTypeSubst env (TRec s t)       = TRec s (globTypeSubst env t)
globTypeSubst env (TGlobTypeVar s) = case lookup s env of
                                           Just(t) -> t
                                           _ -> TGlobTypeVar "not found"
globTypeSubst _ a = a

globTypeInExprSubst :: Env -> Expr -> Expr
globTypeInExprSubst env (ELam s t e) = ELam s (globTypeSubst env t) (globTypeInExprSubst env e)
globTypeInExprSubst env (EApp e1 e2) = EApp (globTypeInExprSubst env e1) (globTypeInExprSubst env e2)
globTypeInExprSubst env (ELet s e1 e2) = ELet s (globTypeInExprSubst env e1) (globTypeInExprSubst env e2)
globTypeInExprSubst env (EIf c e1 e2) = EIf (globTypeInExprSubst env c) (globTypeInExprSubst env e1) (globTypeInExprSubst env e2)
globTypeInExprSubst env (ETuple es) = ETuple (map (globTypeInExprSubst env) es)
globTypeInExprSubst env (ETupProj e1 e2) = ETupProj (globTypeInExprSubst env e1) (globTypeInExprSubst env e2)
globTypeInExprSubst env (ERecord es) = ERecord $ listMapSnd (globTypeInExprSubst env) es
globTypeInExprSubst env (ERecordProj e s) = ERecordProj (globTypeInExprSubst env e) s
globTypeInExprSubst env (ECase e es) = ECase (globTypeInExprSubst env e) (listMapSnd (mapSnd (globTypeInExprSubst env)) es)
globTypeInExprSubst env (ETag s es t) = ETag s (map (globTypeInExprSubst env) es) (globTypeSubst env t)
globTypeInExprSubst env (EFold t) = EFold (globTypeSubst env t)
globTypeInExprSubst env (EUnfold t) = EUnfold (globTypeSubst env t)
globTypeInExprSubst env (ERoot es) = ERoot (map (globTypeInExprSubst env) es)
globTypeInExprSubst env (EData s t) = EData s (globTypeSubst env t)
globTypeInExprSubst env (ELetFun s t e) = ELetFun s (globTypeSubst env t) (globTypeInExprSubst env e)
globTypeInExprSubst _ a = a
 
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
