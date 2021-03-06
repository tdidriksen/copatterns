module TypeChecker where

import Data.Either
import Control.Monad.Error
import Control.Applicative
import Expr
import Data.Graph.Inductive.Query.Monad
import Data.List (sort)

-- Output expression
data TypedExpr
  = TEUnit       Type
  | TEVar        Type Sym
  | TEApp        Type TypedExpr [TypedExpr]
  | TELet        Type Sym Type (Maybe Params) TypedExpr TypedExpr
  | TECase       Type TypedExpr [(Sym, ([Sym], TypedExpr))]
  | TEObserve    Type [(Sym, TypedExpr)]
  | TETag        Type Sym [TypedExpr]
  | TEFold       Type Type
  | TEUnfold     Type Type
  | TEData       Type Sym
  | TECodata     Type Sym
  | TEGlobLet    Type Sym (Maybe Params) TypedExpr
  deriving (Eq, Show)

getTypeAnno :: TypedExpr -> Type
getTypeAnno (TEUnit       t      ) = t
getTypeAnno (TEVar        t _    ) = t
getTypeAnno (TEApp        t _ _  ) = t
getTypeAnno (TELet        t _ _ _ _ _) = t
getTypeAnno (TECase       t _ _  ) = t
getTypeAnno (TEObserve    t _    ) = t
getTypeAnno (TETag        t _ _  ) = t
getTypeAnno (TEFold       t _    ) = t
getTypeAnno (TEUnfold     t _    ) = t
getTypeAnno (TEData       t _    ) = t
getTypeAnno (TECodata     t _    ) = t
getTypeAnno (TEGlobLet    t _ _ _) = t

data TypeError 
  = NotInScope Sym
  | TypeMismatch Type Type
  | TypeNotAllowed Type String
  | Unexpected Type String
  | AnnotationMismatch Type Type String
  | LabelNotFound Sym Type
  | CoverageError [Sym] [Sym]
  | ArgumentMismatch [Type] Params Sym
  | DuplicateName Sym
  | NotValidRootExpr Expr
  | NotValidExpression Expr
  | Err String

instance Show TypeError where
  show (NotInScope               s) = s ++ " not in scope."
  show (TypeMismatch         t1 t2) = "Type mismatch between " ++ (show t1) ++ " and " ++ (show t2) ++ "."
  show (TypeNotAllowed         t s) = "Type " ++ (show t) ++ " not allowed: " ++ s ++ "."
  show (Unexpected             t s) = "Unexpected type " ++ (show t) ++ ". Expected " ++ s ++ "."
  show (AnnotationMismatch t1 t2 s) = "Mismatch between annotated type " ++ (show t1) ++ " and actual type " ++ (show t2) ++ ": " ++ s ++ "."
  show (LabelNotFound          s t) = "Label " ++ s ++ " not found in type " ++ (show t) ++ "."
  show (CoverageError        s1 s2) = "Coverage error between: " ++ (show s1) ++ " and " ++ (show s2) ++ "."
  show (ArgumentMismatch   ts ps s) = "Argument mismatch between: " ++ (show ts) ++ " and " ++ (show ps) ++ " in function " ++ s ++ "."
  show (DuplicateName            s) = "Illigal duplicate name " ++ s ++ "."
  show (NotValidRootExpr         e) = "Expression " ++ (show e) ++ " is not a valid root expression."
  show (NotValidExpression       e) = "Expression " ++ (show e) ++ " is not a valid expression."
  show (Err                      s) = "Error: " ++ s

instance Eq TypeError where
  NotInScope s               == NotInScope s'                =  s == s'
  TypeMismatch t1 t2         == TypeMismatch t1' t2'         = t1 == t1' && t2 == t2'
  TypeNotAllowed t _         == TypeNotAllowed t' _          =  t == t'
  Unexpected t _             == Unexpected t' _              =  t == t'
  AnnotationMismatch t1 t2 _ == AnnotationMismatch t1' t2' _ = t1 == t1' && t2 == t2'
  LabelNotFound s t          == LabelNotFound s' t'          =  s == s'  &&  t == t'
  CoverageError s1 s2        == CoverageError s1' s2'        = s1 == s1' && s2 == s2'
  ArgumentMismatch ts ps s   == ArgumentMismatch ts' ps' s'  = ts == ts' && ps == ps' && s == s'
  DuplicateName s            == DuplicateName s'             =  s == s'
  NotValidRootExpr e         == NotValidRootExpr e'          =  e == e'
  NotValidExpression e       == NotValidExpression e'        =  e == e'
  Err _                      == Err _                        = True
  _                          == _                            = False

instance Error TypeError where
  noMsg = Err ""

------ Typing ------

-- Check Root Expression
checkRoot :: Expr -> Either TypeError [TypedExpr]
checkRoot (ERoot ds) = case buildRootEnv ds of
                         Right l -> do
                          vEnv <- assocDups $ fst l
                          tEnv <- assocDups $ snd l
                          let ts = map (checkDef vEnv tEnv) ds in 
                            case eitherUnzip $ ts of
                              Right ts -> return ts
                              Left err -> throwError err
                         Left err -> throwError err

-- Typing of Expr
check :: Env -> Env -> Expr -> Either TypeError TypedExpr
check _ _ EUnit              = return $ TEUnit TUnit
check vEnv tEnv (EVar x) = case (lookup x vEnv) of
  Just e  -> return $ TEVar (globTypeSubst tEnv e) x
  Nothing -> throwError $ NotInScope x
check vEnv tEnv (EApp e1 e2) = do
  te1 <- check vEnv tEnv e1
  case eitherUnzip $ map (check vEnv tEnv) e2 of
    Right te2 ->
      case getTypeAnno te1 of
        (TArr f a) -> case listTypeEquality f (map getTypeAnno te2) tEnv of
                        Right _ -> return $ TEApp (globTypeSubst tEnv a) te1 te2
                        Left x  -> throwError x
        t -> throwError $ TypeNotAllowed t "Application on non arrow type"
    Left err -> throwError err
check vEnv tEnv (ELet s t ps e1 e2) = 
  let params = case ps of 
                   Just ps' -> ps'
                   Nothing  -> []
  in do
    te1 <- check ((s,t) : (params ++ vEnv)) tEnv e1
    te2 <- check ((s,t) : vEnv) tEnv e2
    case t of 
      TArr as r -> 
          if as == (map snd params)
            then
              case typeEquality r (getTypeAnno te1) tEnv of
                Right _ -> return $ TELet (getTypeAnno te2) s (globTypeSubst tEnv t) ps te1 te2
                Left err -> throwError err
            else
              throwError $ ArgumentMismatch as params s
      _ ->  
          case typeEquality t (getTypeAnno te1) tEnv of
            Right _ -> return $ TELet (getTypeAnno te2) s (globTypeSubst tEnv t) ps te1 te2
            Left err -> throwError err
check vEnv tEnv (ETag s e t) = do
  case t of
    TVari fs ->
      case lookup s fs of
        Just et -> do
          let te = map (check vEnv tEnv) e in
            case eitherUnzip te of
              Right te ->
                case listTypeEquality (map getTypeAnno te) et tEnv of
                  Right _ -> return $ TETag (globTypeSubst tEnv t) s te
                  Left  x -> throwError x
              Left err -> throwError err
        Nothing -> throwError $ LabelNotFound s t
    TGlobTypeVar s       -> do
                          t <- typeVarLookup s tEnv
                          check vEnv tEnv (ETag s e t)
    t -> throwError $ Unexpected t "variant type"
check vEnv tEnv (ECase e es) = do
  te <- check vEnv tEnv e
  case getTypeAnno te of
    (TRecInd s vt) ->
      case vt of
        TVari fs ->
          if (not $ bagEq (map fst fs) (map fst es))
            then throwError $ CoverageError (map fst fs) (map fst es)
            else 
              let vEnvs = map (++ vEnv) (map (\x -> zip (fst x) (snd x)) (assocJoin (listMapSnd fst es) fs)) in
                case eitherUnzip $ zipWith (\v e -> check v tEnv e) vEnvs (map snd (map snd es)) of
                  Right(t : ts) -> --return $ TETag (TGlobTypeVar "nat") (show $  length vEnvs) (t : ts)
                    case eitherUnzip $ map (\t2 -> typeEquality (getTypeAnno t) t2 tEnv) (map getTypeAnno ts) of
                      Right _ -> return $ TECase (getTypeAnno t) te (zip (map fst es) (zip (map fst (map snd es)) (t : ts)))
                      Left err -> throwError err
                  Left err -> throwError err
        t -> throwError $ Unexpected t "variant type"
    t -> throwError $ Unexpected t "inductive type"
check vEnv tEnv (EObserve t es) = do
  case t of
    TRecCoind s fs ->
      if (not $ bagEq (map fst fs) (map fst es))
        then throwError $ CoverageError (map fst fs) (map fst es)
        else
          case eitherUnzip $ map (check vEnv tEnv) (map snd es) of
            Right tes -> 
              case assocJoin (zip (map fst es) tes) (listMapSnd (substTypeVari s t) fs) of
                []     -> throwError $ Err "No observations found"
                xs     -> 
                  case eitherUnzip $ map (\x -> matchTEWithType x tEnv) xs of
                    Right _  -> return $ TEObserve (globTypeSubst tEnv t) (zip (map fst es) tes)
                    Left err -> throwError err
            Left err -> throwError err
    TGlobTypeVar s -> do
                  t <- typeVarLookup s tEnv
                  check vEnv tEnv (EObserve t es)
    t -> throwError $ Unexpected t "coinductive type"
check vEnv tEnv (EFold t) = do
  case t of
    TRecInd s nt -> return $ TEFold (globTypeSubst tEnv (TArr [nt] t)) (globTypeSubst tEnv t)
    TGlobTypeVar s -> do
                  t <- typeVarLookup s tEnv
                  check vEnv tEnv (EFold t)
    t         -> throwError $ Unexpected t "inductive type"
check vEnv tEnv (EUnfold t) = do
  case t of
    TRecInd s nt -> return $ TEUnfold (globTypeSubst tEnv (TArr [t] (TRecInd s (substTypeVari s t nt)))) (globTypeSubst tEnv t)
    TGlobTypeVar s       -> do
                          t <- typeVarLookup s tEnv
                          check vEnv tEnv (EUnfold t)
    t         -> throwError $ Unexpected t "inductive type"
check _ _ e = throwError $ NotValidExpression e

-- Typing definitions
checkDef :: Env -> Env -> Defi -> Either TypeError TypedExpr
checkDef vEnv tEnv (DData s t) = 
  case t of
    TRecInd s' nt | s == s' -> case nt of
                                 TVari fs -> do
                                   lbls <- assocDups fs
                                   return $ TEData (globTypeSubst tEnv (TRecInd s (TVari lbls))) s
                  | otherwise -> throwError $ Err "Data label not matching name of inductive type"
    TGlobTypeVar s       -> do
                          t <- typeVarLookup s tEnv
                          checkDef vEnv tEnv (DData s t)
    t                    -> throwError $ Unexpected t "inductive type"
checkDef vEnv tEnv (DCodata s t) =
  case t of
    TRecCoind s' es | s == s' -> do
                               lbls <- assocDups es
                               return $ TECodata (globTypeSubst tEnv (TRecCoind s lbls)) s
                    | otherwise -> throwError $ Err "Codata label not matching name of coinductive type"
    TGlobTypeVar s       -> do
                          t <- typeVarLookup s tEnv
                          checkDef vEnv tEnv (DCodata s t)
    t                    -> throwError $ Unexpected t "coinductive type"
checkDef vEnv tEnv (DGlobLet s t ps e) = do
  te <- check (maybeAppend ps vEnv) tEnv e
  case ps of
    Just ps ->
      case t of
        TArr a r -> 
          if not (a == (map snd ps)) then throwError $ ArgumentMismatch a ps s
          else case typeEquality r (getTypeAnno te) tEnv of
            Right  _ -> return $ TEGlobLet (globTypeSubst tEnv (TArr a r)) s (Just ps) te
            Left err -> throwError err
        t -> throwError $ Unexpected t "arrow type"
    Nothing ->
      case typeEquality (getTypeAnno te) t tEnv of
        Right _  -> return $ TEGlobLet t s ps te
        Left err -> throwError err


-- Looks up a symbol in the environment. Throws NotInScope error if not found.
typeVarLookup :: Sym -> Env -> Either TypeError Type
typeVarLookup s env = case lookup s env of
                       Just(t) -> return t
                       Nothing -> throwError $ NotInScope s

-- Type equality
typeEquality :: Type -> Type -> Env -> Either TypeError Type
typeEquality t1 t2 env | (globTypeSubst env t1) == (globTypeSubst env t2) = return t1
                       | otherwise = throwError $ TypeMismatch (globTypeSubst env t1) (globTypeSubst env t2)

-- Type equality for lists of types
listTypeEquality :: [Type] -> [Type] -> Env -> Either TypeError [Type]
listTypeEquality (x : xs) (y : ys) env = do
  t <- (typeEquality x y env)
  ts <- (listTypeEquality xs ys env)
  return $ t : ts
listTypeEquality [] [] env = return []
listTypeEquality xs ys env = throwError $ Err $ "Type mismatch on lists: " ++ (show xs) ++ " and " ++ (show ys)

isNotArrowType :: Type -> Either TypeError Type
isNotArrowType (TArr t1 t2) = throwError $ (TypeNotAllowed (TArr t1 t2) "Arrow type not allowed")
isNotArrowType t            = return t

-- Matches the type of a TypedExpr with another type.
matchTEWithType :: (TypedExpr, Type) -> Env -> Either TypeError Type
matchTEWithType (te, t) = typeEquality (getTypeAnno te) t

-- Substitutes recursive type variables
substTypeVari :: Sym -> Type -> Type -> Type
substTypeVari s t (TArr  t1 t2) = TArr (map (substTypeVari s t) t1) (substTypeVari s t t2)
substTypeVari s t (TVari    ts) = TVari   $ listMapSnd (map $ substTypeVari s t) ts
substTypeVari s t (TRecInd s' t') = TRecInd s' (substTypeVari s t t')
substTypeVari s t (TRecTypeVar s') | s == s' = t
substTypeVari _ _ a = a

-- Substitutes global type variables
globTypeSubst :: Env -> Type -> Type
globTypeSubst env (TArr t1 t2)     = TArr (map (globTypeSubst env) t1) (globTypeSubst env t2)
globTypeSubst env (TVari ts)       = TVari $ listMapSnd (map $ globTypeSubst env) ts
globTypeSubst env (TRecInd s t)    = TRecInd s (globTypeSubst env t)
globTypeSubst env (TGlobTypeVar s) = case lookup s env of
                                           Just(t) -> globTypeSubst env t
                                           _ -> TGlobTypeVar "not found"
globTypeSubst _ a = a
 
-- Build Root Environment. Used for before type checking to build global environment.
buildRootEnv :: [Defi] -> Either TypeError (Env, Env)
buildRootEnv []       = Right ([], [])
buildRootEnv (x : xs) = case buildRootEnv xs of
                          Right l -> 
                            case x of
                              DData    s t   -> return $ ((listMapSnd reduceArrows (typeFunctions t)) ++ (fst l), (s, t) : (snd l))
                              DCodata  s t   -> return $ ((typeFunctions t) ++ (fst l), (s, t) : (snd l))
                              DGlobLet s t _ _ -> return $ ((s, t) : (fst l), snd l)
                             -- e             -> throwError $ NotValidRootExpr e
                          Left  e -> throwError e

-- Creates functions for constructors and destructors
typeFunctions :: Type -> [(Sym, Type)]
typeFunctions (TRecInd s t)   = case t of 
                                  TVari fs ->
                                    listMapSnd (\x -> TArr (map (\y -> substTypeVari s (TGlobTypeVar s) y) x) (TGlobTypeVar s)) fs
                                  _ -> []
typeFunctions (TRecCoind s es) = listMapSnd (\x -> TArr [(TGlobTypeVar s)] (substTypeVari s (TGlobTypeVar s) x)) es
typeFunctions _ = []

-- Reduces arrow types with no parameters.
reduceArrows :: Type -> Type
reduceArrows (TArr t1 t2)     = case t1 of
                                  [] -> t2
                                  _  -> TArr (map reduceArrows t1) t2
reduceArrows (TVari ts)       = TVari (listMapSnd (map reduceArrows) ts)
reduceArrows (TRecInd s t)    = TRecInd s (reduceArrows t)
reduceArrows (TRecCoind s es) = TRecCoind s (listMapSnd reduceArrows es)
reduceArrows a = a

-- Finds duplicates in environments.
assocDups :: [(Sym, a)] -> Either TypeError [(Sym, a)]
assocDups (x : []) = return $ [x]
assocDups (x : xs) = case lookup (fst x) xs of
                                      Just _ -> throwError $ DuplicateName (fst x)
                                      Nothing -> do
                                        rest <- assocDups xs
                                        return $ x : rest
assocDups _ = throwError $ Err "No symbols"

------ Util ------

-- Maps a function over the first element of a list of pairs
listMapFst :: (a -> c) -> [(a, b)] -> [(c, b)]
listMapFst f p = zip (map f (fst $ unzip p)) (snd $ unzip p)

-- Maps a function over the second element of a list of pairs
listMapSnd :: (b -> c) -> [(a, b)] -> [(a, c)]
listMapSnd f p = zip (fst $ unzip p) (map f (snd $ unzip p))

eitherUnzip :: [Either a b] -> Either a [b]
eitherUnzip []       = return []
eitherUnzip (x : xs) = case x of 
                        Left e  -> Left e
                        Right t -> do
                          ts <- eitherUnzip xs
                          return $ t : ts

bagEq :: Ord a => [a] -> [a] -> Bool
bagEq xs ys = sort xs == sort ys

maybeAppend :: Maybe [a] -> [a] -> [a]
maybeAppend (Just xs) ys = xs ++ ys
maybeAppend Nothing   ys =       ys

assocJoin :: Eq a => [(a, b)] -> [(a, c)] -> [(b, c)]
assocJoin [] ys       = []
assocJoin (x : xs) ys = case lookup (fst x) ys of
                          Just y  -> (snd x, y) : assocJoin xs ys
                          Nothing -> error $ "Not found"

pairConcat :: [([a], [b])] -> [(a, b)]
pairConcat [] = []
pairConcat (x : xs) = zip (fst x) (snd x) ++ (pairConcat xs)
        
