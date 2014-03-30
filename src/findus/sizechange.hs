module TerminationChecker where

import Findus
import TypeChecker
import Examples

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
splitInput []                           = ([], [])
splitInput (gl@(TEGlobLet _ _ _ _) : tes) = (fst $ splitInput tes, gl : (snd $ splitInput tes))
splitInput (dt@(TEData _ _)      : tes) = (dt : (fst $ splitInput tes), snd $ splitInput tes)
splitInput (_                    : tes) = splitInput tes

-- Size terms

data Size =
    Param Sym                  -- Function parameter
  | Var Sym Size           -- Introduced local variable
  | Value TypedExpr DataEnv    -- Expression with environment
  | Min                        -- Minimal value, e.g. Z for Nat and Nil for List
  | Unknown                    -- When the size is unknown
  | C Size                 -- Constructor application. C (Param "x") > Param "x"
  | D Size                 -- Destructor. D (Param "x") < Param "x"
  | Multiple [Size]        -- Non-deterministic choice. Used when a term can have several possible sizes. 


-- Control-flow graphs

-- Control points represent the terms that must terminate
data ControlPoint a = Global Sym a | Local Sym (ControlPoint a) a deriving Eq

-- A Call is a connection between two control points, establishing interdependency
type CallLabel = String
type Call a = (ControlPoint a, a, ControlPoint a)
type CallSequence a = [Call a]

transitiveCall :: Call a -> Call a -> Maybe (CallSequence a)
transitiveCall x y = Nothing -- TODO

isRecursiveTransitive :: CallSequence a -> Bool
isRecursiveTransitive x = False -- TODO

isReachable :: Call a -> Bool -- Is the call reachable from the main function
isReachable x = False

type ControlFlowEntry a = (ControlPoint a, [Call a])
type ControlFlowGraph a = [ControlFlowEntry a]


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

controlFlowGraph :: ControlPoint DataEnv -> TypedExpr -> [ControlPoint DataEnv] -> DataEnv -> [Call DataEnv]
controlFlowGraph f (TEApp ty fun args) cps dataenv = [] -- TODO
controlFlowGraph f (TELet ty sym exprty p expr body) cps dataenv =
  let params = paramsAsData p in
  let localdef = Local sym f params
  in controlFlowGraph localdef expr (localdef : cps) (params ++ dataenv)
     ++ controlFlowGraph f body (localdef : cps) dataenv
controlFlowGraph f (TEIf ty c tb fb) cps dataenv =
  foldl (++) [] $ map (\e -> controlFlowGraph f e cps dataenv) [c, tb, fb]
controlFlowGraph f (TETuple ty exprs) cps dataenv =
  foldl (++) [] $ map (\e -> controlFlowGraph f e cps dataenv) exprs
controlFlowGraph f (TERecord ty exprs) cps dataenv =
  foldl (++) [] $ map (\(_, e) -> controlFlowGraph f e cps dataenv) exprs
controlFlowGraph f (TECase ty expr cases) cps dataenv = []
  --case expr of
    
controlFlowGraph f@(Global id dataenv) (TEGlobLet _ id' _ body) cps []
  | id == id' = controlFlowGraph f body cps dataenv
  | otherwise = []

sizeOf :: TypedExpr -> DataEnv -> Size
sizeOf (TEVar _ id) env =
  case lookup id env of
    Just (DataPos st) -> st
    Nothing -> Unknown -- If we cannot say anything, we must assume the worst
sizeOf (TEApp _ (TEFold _ _) [(TETag _ _ targs)]) env = Unknown -- Hvilke typer skal sammenlignes?
sizeOf (TEApp _ (TEUnfold _ _) args) env = Unknown
sizeOf (TEApp _ _ _) env = Unknown
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
