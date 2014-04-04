module TerminationChecker where

import Findus
import TypeChecker
import Data.List

-- eval : Expr -> Value* -> Value#
-- Value# = Z + {}
-- Program points: The points where function calls can occur - must be finite
-- Call: Program point 1 -- label -- > program point 2
-- Transitive calls -- call sequence
-- State transitions
-- Size-change graphs

-- Graph-basis: The set of things on either side of a transition in a size-change graph
-- Arc in size-change graph from p1 to p2: gb(p1) x { down, eq } x gb(p2)

-- Handle input

splitInput :: [TypedExpr] -> ([TypedExpr], [TypedExpr])
splitInput []                             = ([], [])
splitInput (gl@(TEGlobLet _ _ _ _) : tes) = (fst $ splitInput tes, gl : (snd $ splitInput tes))
splitInput (dt@(TEData _ _)        : tes) = (dt : (fst $ splitInput tes), snd $ splitInput tes)
splitInput (_                      : tes) = splitInput tes

-- Size terms

data Size =
    Min                    -- Minimal value, e.g. Z for Nat and Nil for List
  | D Size                 -- Destructor. D (Param "x") < Param "x"
  | Param Sym              -- Function parameter
  | Var Sym                -- Non-parameter value
  | C Size                 -- Constructor application. C (Param "x") > Param "x"
  | Unknown                -- When the size is unknown
  | Multiple [Size]        -- Non-deterministic choice. Used when a term can have several possible sizes.
  | Alias Size Size        -- When one size might act as an alias for another. Mostly used for base cases.
  deriving Eq

instance Ord Size where
  -- Min
  compare Min       Min        = EQ
  compare Min       _          = LT
  -- Destructors
  compare (D s)     (D s')     = compare s s'
  compare (D (C s)) s'         = compare s s'
  compare s         (D (C s')) = compare s s'
  compare (D s)     Min        = GT
  compare (D s)     (C s')     = if s == s' then compare s s' else LT
  compare (D s)     _          = LT
  -- Param
  compare (Param x) (Param y)  = if x == y then EQ else GT
  compare (Param x) Min        = GT
  compare (Param x) (D s)      = GT
  compare (Param x) _          = LT
  -- Var
  compare (Var x)   (Var y)    = if x == y then EQ else GT
  compare (Var x)   Min        = GT
  compare (Var x)   (D s)      = GT
  compare (Var x)   _          = LT
  -- Constructors
  compare (C s)     (C s')     = compare s s'
  compare (C (D s)) s'         = compare s s'
  compare s         (C (D s')) = compare s s'
  compare (C s)     Min        = GT
  compare (C s)     (D s')     = if s == s' then compare s s' else GT
  compare (C s)     (Param x)  = GT
  compare (C s)     (Var x)    = GT
  compare (C s)     _          = LT
  -- Unknown
  compare Unknown   Unknown    = EQ
  compare _         Unknown    = LT
  -- Multiple
  compare (Multiple ss) s'     = foldl1 compare (map (\s'' -> compare s'' s') ss)
  compare s     (Multiple ss') = foldl1 compare (map (compare s) ss')
  -- Alias
  compare (Alias s s') s''     = compare s' s''
  compare s     (Alias s' s'') = compare s s''
  -- Catch-all
  compare _         _          = GT

  
-- Control-flow graphs

-- Control points represent the terms that must terminate
data ControlPoint a = Global Sym a | Local Sym (ControlPoint a) a deriving Eq

-- A Call is a connection between two control points, establishing interdependency
type CallLabel = String
type Substitution a = [(DataPosition a, DataPosition a)]
type Call a b = (ControlPoint a, b, ControlPoint a)
type CallSequence a b = [Call a b]

transitiveCall :: Call a b -> Call a b -> Maybe (CallSequence a b)
transitiveCall x y = Nothing -- TODO

isRecursiveTransitive :: CallSequence a b -> Bool
isRecursiveTransitive x = False -- TODO

isReachable :: Call a b -> Bool -- Is the call reachable from the main function
isReachable x = False

type ControlFlowGraph a b = [Call a b]

controlPointId :: ControlPoint a -> Sym
controlPointId (Global id _) = id
controlPointId (Local id _ _) = id

controlPointData :: ControlPoint a -> a
controlPointData (Global _ a)  = a
controlPointData (Local _ _ a) = a


-- Size-change graphs

data Arrow = Descending | NonIncreasing | Absent deriving Eq

-- Data positions represent the terms that (may) change size
data DataPosition a = DataPos a deriving Eq

-- A size-change arc describes a change between two data positions
type SCArc a = (DataPosition a, Arrow, DataPosition a)

-- A size-change graph is a set of size-change arcs. Data positions are included here for later consistency checks.
type SizeChangeGraph a = ([DataPosition a], [SCArc a], [DataPosition a])

type MultiPath a = [SizeChangeGraph a]

type Thread a = [SCArc a]

-- Functions on size-change graphs

areComposable :: Eq a => SizeChangeGraph a -> SizeChangeGraph a -> Bool
areComposable (_, _, y) (y', _, _) = y == y'

compose :: Eq a => SizeChangeGraph a -> SizeChangeGraph a -> Maybe (SizeChangeGraph a)
compose g@(x, xy, y) g'@(y', yz, z)
  | areComposable g g' = Just (x, composeArrows xy yz, z)
  | otherwise          = Nothing
  where
    composeArrows :: Eq a => [SCArc a] -> [SCArc a] -> [SCArc a]
    composeArrows xy yz =
          [ (x, Descending   , z) | (x, arr, y) <- xy, (y', arr', z) <- yz, y == y',
                                    arr == Descending || arr' == Descending       ] ++
          [ (x, NonIncreasing, z) | (x, arr, y) <- xy, (y', arr', z) <- yz, y == y',
                                    arr == NonIncreasing && arr' == NonIncreasing ] ++
          [ (x, Absent       , z) | (x, arr, y) <- xy, (y', arr', z) <- yz, y == y',
                                    arr == Absent || arr' == Absent               ]


hasArc :: Eq a => SizeChangeGraph a -> SCArc a -> Bool
hasArc (_, arcs, _) arc = any (== arc) arcs

isSafe :: (Eq a, Ord a) => SizeChangeGraph a -> Bool
isSafe (as, arcs, bs) = all (\arc -> isSafeArc as arc bs) arcs && hasConsistentArcs arcs
 where
   isSafeArc :: (Eq a, Ord a) => [DataPosition a] -> SCArc a -> [DataPosition a] -> Bool
   isSafeArc as (DataPos a', arrow, DataPos b') bs =
     DataPos a' `elem` as && DataPos b' `elem` bs && case arrow of
                                                       Descending    -> a' < b'
                                                       NonIncreasing -> a' <= b'
                                                       Absent        -> a' > b'
   hasConsistentArcs :: Eq a => [SCArc a] -> Bool -- Consistency = no duplicate arcs with different arrows
   hasConsistentArcs arcs = null $ [ (a, y) | (a, arr, b) <- arcs, (x, arr', y) <- arcs, a == x, b == y, not (arr == arr') ]

-- Building size-change graphs
    -- 1. Build control-flow graph, CFG
    -- 2. For each activable/reachable call in CFG, generate a size-change graph,
    --    obtaining a set of size-change graphs, G
    -- 3. Build the transitive closure of G, Gtrans, by size-change graph composition
    -- 4. 

-- Functions on threads

isDescending :: Thread a -> Bool
isDescending []                          = False
isDescending ((_, Descending, _) : arcs) = True
isDescending (_ : arcs)                  = isDescending arcs

isInfinitelyDescending :: Thread a -> Bool
isInfinitelyDescending x = False -- TODO


-- Implementation-specific functions

-- All control points have a set of initial data positions
-- All data positions have a size
-- All calls map arguments to data positions

type DataEnv = [(Sym, DataPosition Size)]


paramsAsData :: Maybe Params -> [(Sym, DataPosition Size)]
paramsAsData Nothing       = []
paramsAsData (Just params) = map (\(sym, _) -> (sym, DataPos $ Param sym)) params

globalControlPoints :: [TypedExpr] -> [(ControlPoint DataEnv, TypedExpr)]
globalControlPoints (TEGlobLet ty name params body : globs) =
  (Global name (paramsAsData params), body) : globalControlPoints globs
globalControlPoints (_ : globs) = globalControlPoints globs

dataEnv :: ControlPoint DataEnv -> DataEnv
dataEnv (Global _ env)  = env
dataEnv (Local _ parent env) = env ++ dataEnv parent

-- If no local dataenv, then control point is value

controlPointsFromExpr :: TypedExpr -> [ControlPoint a] -> [ControlPoint a]
controlPointsFromExpr (TEVar f) cps =
  case find (\cp -> f == controlPointId cp) cps of
    Just cp = [cp]
    Nothing = []
controlPointsFromExpr _ _ = error "Bad control point"

controlFlowGraph :: ControlPoint DataEnv -> TypedExpr -> [(ControlPoint DataEnv, Maybe Size)] -> DataEnv -> [Call DataEnv (Substitution DataEnv)]
controlFlowGraph f (TEApp _ (TEFold _ _) [tag@(TETag _ _ _)]) cps dataenv = controlFlowGraph f tag cps dataenv
controlFlowGraph f (TEApp _ (TEUnfold _ _) [arg]) cps dataenv = controlFlowGraph f arg cps dataenv 
controlFlowGraph f (TEApp _ g args) cps dataenv =
  let calledFunctions = controlPointsFromExpr g $ map fst cps
  in let calleeData cp = controlPointData cp
  in 
  in let call h = (f, zip (calleeData h) , h)
controlFlowGraph f (TELet ty id exprty params expr body) cps dataenv =
  let paramData = paramsAsData params
  in let localDef = Local id f paramData
  in let exprGraph = controlFlowGraph localDef expr ((localDef, Nothing) : cps) (paramData ++ dataenv)
  in let exprSize = sizeOf expr (paramData ++ dataenv)
  in case exprGraph of
       [] -> case params of
               Just ps -> controlFlowGraph f body ((localDef, exprSize) : cps) dataenv
               Nothing -> controlFlowGraph f body cps ((id, DataPos exprSize) : dataenv)
       eg -> eg ++ controlFlowGraph f body ((localDef, Nothing) : cps) dataenv 
controlFlowGraph f (TEIf ty c tb fb) cps dataenv =
  foldl (++) [] $ map (\e -> controlFlowGraph f e cps dataenv) [c, tb, fb]
controlFlowGraph f (TETuple ty exprs) cps dataenv =
  foldl (++) [] $ map (\e -> controlFlowGraph f e cps dataenv) exprs
controlFlowGraph f (TERecord ty exprs) cps dataenv =
  foldl (++) [] $ map (\(_, e) -> controlFlowGraph f e cps dataenv) exprs
controlFlowGraph f (TECase ty expr cases) cps dataenv =
  let exprSize = sizeOf expr dataenv
  in let exprType = getTypeAnno expr
  in let variant = case exprType of
                     TVari ts          -> ts
                     TRec _ (TVari ts) -> ts
                     _                 -> error "Matched expression is not a variant type" -- TODO
  in let caseTypes id = case lookup id variant of
                          Just tys -> tys
                          Nothing  -> error "Incompatible pattern"
  in let annotatedVars (id, (vars, _)) = zip vars (caseTypes id)
  in let isRecType = (== exprType)
  in let argEnv c = map (\(v, t) -> if isRecType t then (v, DataPos $ D exprSize) else (v, DataPos $ Var v)) (annotatedVars c)
  in let isBaseCase c = null $ filter (\(v,t) -> isRecType t) (annotatedVars c) 
  in let (baseCases, recCases) = partition isBaseCase cases
  in let caseExpr = snd . snd
  in let baseGraph = map (\c -> controlFlowGraph f (caseExpr c) cps (("", DataPos $ Alias Min exprSize) : argEnv c ++ dataenv)) baseCases
  in let recGraph = map (\c -> controlFlowGraph f (caseExpr c) cps (argEnv c ++ dataenv)) recCases
  in foldl (++) [] $ baseGraph ++ recGraph
controlFlowGraph f (TETag ty id args) cps dataenv = 
  foldl (++) [] $ map (\arg -> controlFlowGraph f arg cps dataenv) args
controlFlowGraph f@(Global id dataenv) (TEGlobLet _ id' _ body) cps []
  | id == id' = controlFlowGraph f body cps dataenv
  | otherwise = []
controlFlowGraph _ _ _ _ = []


sizeOf :: TypedExpr -> DataEnv -> Size
sizeOf (TEVar _ id) env =
  case lookup id env of
    Just (DataPos st)          -> st
    Nothing                    -> Unknown -- If we cannot say anything, we must assume the worst
sizeOf (TEApp _ (TEFold _ _) [tag@(TETag _ _ _)]) env = sizeOf tag env
sizeOf (TEApp _ (TEUnfold _ _) [arg]) env = sizeOf arg env
sizeOf (TEApp _ _ _) env = Unknown
sizeOf (TELet _ id _ p expr body) env =
  let params = paramsAsData p
  in let exprSize = sizeOf expr (params ++ env)
  in sizeOf body ((id, DataPos exprSize) : env)
sizeOf (TEIf _ c tb fb) env =
  let trueBranchSize = sizeOf tb env
  in let falseBranchSize = sizeOf fb env
  in max trueBranchSize falseBranchSize
sizeOf (TETuple _ exprs) env =
  case exprs of
    []  -> Unknown
    [e] -> sizeOf e env
    es  -> Multiple $ map (\e -> sizeOf e env) es
-- Tuple projection, records, record projection?
sizeOf (TECase _ expr cases) env =
  let exprSize = sizeOf expr env
  in let exprType = getTypeAnno expr
  in let variant = case exprType of
                     TVari ts          -> ts
                     TRec _ (TVari ts) -> ts
                     _                 -> error "Matched expression is not a variant type" -- TODO
  in let caseTypes id = case lookup id variant of
                          Just tys -> tys
                          Nothing  -> error "Incompatible pattern"
  in let annoVars (id, (vars, _)) = zip vars (caseTypes id)
  in let isRecType = (== exprType)
  in let argEnv c = map (\(v, t) -> if isRecType t then (v, DataPos $ D exprSize) else (v, DataPos $ Var v)) (annoVars c)
  in let caseExpr = snd . snd
  in let recCaseSize c = sizeOf (caseExpr c) $ (argEnv c) ++ env
  in let baseCaseSize c = sizeOf (caseExpr c) $ (("", DataPos $ Alias Min exprSize) : argEnv c) ++ env
  in let isBaseCase c = null $ filter (\(v,t) -> isRecType t) (annoVars c)
  in let (baseCases, recCases) = partition isBaseCase cases
  in let baseCaseSizes = map baseCaseSize baseCases
  in let recCaseSizes = map recCaseSize recCases
  in let nonTrivialBaseSizes = filter (\s -> not $ s == exprSize) baseCaseSizes
  in let caseSizes = nonTrivialBaseSizes ++ recCaseSizes
  in let maxSize = if null caseSizes then Unknown else foldr1 max caseSizes -- Gør det mest konservative.
  in maxSize
sizeOf (TETag tagty id args) env =
  let hasTaggedType arg = case getTypeAnno arg of
                            vari@(TVari _) -> vari == tagty
                            TRec _ vari    -> vari == tagty
                            _              -> False
  in let sizeChangingArgs = filter hasTaggedType args
  in case sizeChangingArgs of
       []    -> aliasedSize env Min
       [arg] -> C (sizeOf arg env)
       args  -> Multiple $ map (\arg -> C (sizeOf arg env)) args
 where
  aliasedSize :: DataEnv -> Size -> Size
  aliasedSize env s =
    let isAliasFor size s = case size of
                              Alias a b -> a == s
                              _         -> False
    in case find (\(v, DataPos size) -> null v && isAliasFor size s) env of
         Just ("", DataPos (Alias a b)) -> b
         _                              -> s
sizeOf _ _ = Unknown


-- controlFlowGraph :: [TypedExpr] -> [ControlPoint DataEnv] -> DataEnv -> ControlFlowGraph DataEnv



-- controlFlowGraph :: [(ControlPoint DataEnv, TypedExpr)] -> -> ControlFlowGraph DataEnv
-- controlFlowGraph cps = concat $ map (\(cp, body) -> controlFlow cp (map fst cps) (dataEnv cp) body) cps
--  where
--    controlFlow :: ControlPoint DataEnv -> TypedExpr -> [ControlPoint DataEnv] -> DataEnv -> ControlFlowGraph DataEnv
--    controlFlow cp (TELet ty name params (TArr _ _) expr body) cpenv denv =
--      let localcp = (Local name cp denv) in
--        controlFlow localcp expr (localcp : cpenv) (paramsAsData params : denv) : controlFlow cp body (localcp : cpenv) denv
   

-- initialControlPoints :: [TypedExpr] -> [ControlPoint TypedExpr]
-- initialControlPoints tes = map ControlPoint tes

-- callsForControlPoint :: ControlPoint TypedExpr -> TypedExpr -> [ControlPoint TypedExpr] -> [Call TypedExpr]
-- callsForControlPoint (ControlPoint cp) () = 

-- controlFlowGraph :: TypedExpr -> ControlFlowGraph TypedExpr
-- controlFlowGraph 




-- controlPoints :: TypedExpr -> [TypedExpr]
-- controlPoints global@(TELetFun _ _ body)           = global : controlPoints body
-- controlPoints (TELam funType var (TArr t t') body) = TEVar (TArr t t') var : controlPoints body
-- controlPoints (TELam funType _   _           body) = controlPoints body
-- controlPoints (TELet _ var varExpr body)           = case getTypeAnno varExpr of
--                                                        TArr t t' -> TEVar (TArr t t') var : controlPoints body
                                                       
--                                                        _         -> controlPoints body

-- controlPoints _                                    = []


-- -- subexpressions

-- subexpr :: TypedExpr -> [TypedExpr]
-- subexpr unit@(TEUnit t)                                        = [ unit ]
-- subexpr var@(TEVar t s)                                        = [ var ]
-- subexpr (TELam t s argT body)                                  = [ body ]
-- subexpr (TEApp t f arg)                                        = [ f, arg ]
-- subexpr lit@(TELit t l)                                        = [ lit ]
-- subexpr (TELet t x xexp body)                                  = [ ]
-- subexpr (TEIf t cond tbr fbr)                                  = [ cond, tbr, fbr ]
-- subexpr (TETuple t elems)                                      = elems
-- subexpr (TETupProj t (TETuple t' elems) (TELit TInt (LInt i))) = [ elems !! i ]
-- subexpr (TERecord t elems)                                     = (map snd elems)
--subexpr (TERecordProj t elems sym)                             = 
