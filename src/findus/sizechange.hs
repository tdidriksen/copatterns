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
  | Deferred TypedExpr
  deriving Eq

type Alias = (Size, Size)
withAlias :: Size -> Alias -> Size
withAlias Min       (Min, s)     = s
withAlias (D s)     (D s', s'')  = s `withAlias` (s', s'')
withAlias (Param x) (Param y, s) = if x == y then s else Param x
withAlias (Var x)   (Var y, s)   = if x == y then s else Var x
withAlias (C s)     (C s', s'')  = s `withAlias` (s', s'')
withAlias (Multiple ss) (s, s')  = Multiple $ map (\t -> t `withAlias` (s, s')) ss
withAlias s _ = s

instance Ord Size where -- TODO: Compare skal give mening!
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
type Hints = [(TypedExpr, Sym)]


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

controlPointFromExpr :: TypedExpr -> [ControlPoint a] -> Maybe (ControlPoint a)
controlPointFromExpr (TEVar _ f) cps = find (\cp -> f == controlPointId cp) cps
controlPointFromExpr _ _ = Nothing

controlFlowGraph :: ControlPoint DataEnv -> TypedExpr -> [ControlPoint DataEnv] -> DataEnv -> Hints -> [Call DataEnv (Substitution Size)]
controlFlowGraph f (TEApp _ (TEFold _ _) [tag@(TETag _ _ _)]) cps dataenv hints = controlFlowGraph f tag cps dataenv hints
controlFlowGraph f (TEApp _ (TEUnfold _ _) [arg]) cps dataenv hints = controlFlowGraph f arg cps dataenv hints
controlFlowGraph f (TEApp _ g args) cps dataenv hints =
  let target = case controlPointFromExpr g cps of
                 Just cp -> cp
                 Nothing -> error "Called function does not exist"
  in let targetData cp = map snd $ controlPointData cp
  in let argPositions = map (\arg -> DataPos $ sizeOf arg f cps dataenv hints) args
  in let call h = (f, zip (targetData h) argPositions, h)
  in call target : (foldl (++) [] $ map (\arg -> controlFlowGraph f arg cps dataenv hints) args)
controlFlowGraph f (TELet ty id exprty params expr body) cps dataenv hints =
  let paramData = paramsAsData params
  in let localDef = Local id f paramData
  in let exprGraph = controlFlowGraph localDef expr (localDef : cps) (paramData ++ dataenv) hints
  in let exprSize = sizeOf expr f cps (paramData ++ dataenv) hints
  in case exprGraph of
       [] -> case params of
               Just ps -> controlFlowGraph f body (localDef : cps) ((id, DataPos $ Deferred body) : dataenv) hints
               Nothing -> controlFlowGraph f body cps ((id, DataPos exprSize) : dataenv) hints
       eg -> eg ++ controlFlowGraph f body (localDef : cps) dataenv hints
controlFlowGraph f (TEIf ty c tb fb) cps dataenv hints =
  foldl (++) [] $ map (\e -> controlFlowGraph f e cps dataenv hints) [c, tb, fb]
controlFlowGraph f (TETuple ty exprs) cps dataenv hints =
  foldl (++) [] $ map (\e -> controlFlowGraph f e cps dataenv hints) exprs
controlFlowGraph f (TERecord ty exprs) cps dataenv hints =
  foldl (++) [] $ map (\(_, e) -> controlFlowGraph f e cps dataenv hints) exprs
controlFlowGraph f (TECase ty expr cases) cps dataenv hints =
  let exprSize = sizeOf expr f cps dataenv hints
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
  in let caseExpr = snd . snd
  in let constructor = fst
  in let caseGraphs = map (\c -> controlFlowGraph f (caseExpr c) cps (argEnv c ++ dataenv) ((expr, constructor c) : hints)) cases
  in foldl (++) [] $ caseGraphs
controlFlowGraph f (TETag ty id args) cps dataenv hints = 
  foldl (++) [] $ map (\arg -> controlFlowGraph f arg cps dataenv hints) args
controlFlowGraph f@(Global id dataenv) (TEGlobLet _ id' _ body) cps [] hints
  | id == id' = controlFlowGraph f body cps dataenv hints
  | otherwise = []
controlFlowGraph _ _ _ _ _ = []


sizeOf :: TypedExpr -> ControlPoint DataEnv -> [ControlPoint DataEnv] -> DataEnv -> Hints -> Size
sizeOf (TEVar _ id) f cps env hints =
  case lookup id env of
    Just (DataPos (Deferred e)) -> sizeOf e f cps env hints
    Just (DataPos s)            -> s
    Nothing                     -> Unknown
sizeOf (TEApp _ (TEFold _ _) [tag@(TETag _ _ _)]) f cps env hints = sizeOf tag f cps env hints
sizeOf (TEApp _ (TEUnfold _ _) [arg]) f cps env hints = sizeOf arg f cps env hints
sizeOf (TEApp _ f args) cp cps env hints =
  let target = case controlPointFromExpr f cps of
                 Just cp -> cp
                 Nothing -> error "Called function does not exist"
  in let targetData = controlPointData target
  in sizeOf f cp cps (zip (map fst targetData) (map (\arg -> DataPos $ sizeOf arg cp cps env hints) args) ++ env) hints
sizeOf (TELet _ id _ p expr body) f cps env hints =
  let params = paramsAsData p
  in let localDef = Local id f params
  in let exprSize = sizeOf expr localDef (localDef : cps) (params ++ env) hints
  in sizeOf body f cps ((id, DataPos exprSize) : env) hints
sizeOf (TECase _ expr cases) f cps env hints =
  let exprSize = sizeOf expr f cps env hints
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
  in let constructor = fst
  in let caseExpr = snd . snd
  in let baseCaseSize c = (sizeOf (caseExpr c) f cps ((argEnv c) ++ env) hints) `withAlias` (Min, exprSize)
  in let recCaseSize c = sizeOf (caseExpr c) f cps ((argEnv c) ++ env) hints
  in let isBaseCase c = all (\(v,t) -> not $ isRecType t) (annoVars c)
  in let (baseCases, recCases) = partition isBaseCase cases
  in let baseCaseSizes = map baseCaseSize baseCases
  in let recCaseSizes = map recCaseSize recCases
  in let caseSizes = baseCaseSizes ++ recCaseSizes
  in let maxSize = if null caseSizes then Unknown else foldr1 max caseSizes -- Gør det mest konservative.
  in case lookup expr hints of
       Just hint ->
         case find (\c -> constructor c == hint) cases of
           Just c -> if isBaseCase c then baseCaseSize c else recCaseSize c
           Nothing -> maxSize
       Nothing -> maxSize
sizeOf (TETag tagty id args) f cps env hints =
  let hasTaggedType arg = case getTypeAnno arg of
                            vari@(TVari _) -> vari == tagty
                            TRec _ vari    -> vari == tagty
                            _              -> False
  in let sizeChangingArgs = filter hasTaggedType args
  in case sizeChangingArgs of
       []    -> Min
       [arg] -> C (sizeOf arg f cps env hints)
       args  -> Multiple $ map (\arg -> C (sizeOf arg f cps env hints)) args
sizeOf _ _ _ _ _ = Unknown


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
