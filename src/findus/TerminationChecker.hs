module TerminationChecker where

import Expr
import TypeChecker
import Data.List
import Data.Maybe
import Control.Monad
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.Identity


-- eval : Expr -> Value* -> Value#
-- Value# = Z + {}
-- Program points: The points where function calls can occur - must be finite
-- Call: Program point 1 -- label -- > program point 2
-- Transitive calls -- call sequence
-- State transitions
-- Size-change graphs

-- Graph-basis: The set of things on either side of a transition in a size-change graph
-- Arc in size-change graph from p1 to p2: gb(p1) x { down, eq } x gb(p2)

-- General functions

-- | Finds the sublist starting from the first element for which the predicate holds.
subListFrom :: (a -> Bool) -> [a] -> [a]
subListFrom f     [] = []
subListFrom f (x:xs) = if f x then x : xs else subListFrom f xs

-- | Creates an association list from a list of triples
assocListFromTriples :: (Eq a, Ord a) => [(a, b, c)] -> [(a, [(a, b, c)])]
assocListFromTriples [] = []
assocListFromTriples xs =
  let groups = groupBy (\(a,_,_) -> \(d,_,_) -> a == d) $
               sortBy (\(a,_,_) -> \(d,_,_) -> compare a d) xs
      tripleFst (a,_,_) = a
  in map (\group -> (tripleFst $ head group, group)) groups

-- Handle input

type Program = [TypedExpr]

-- Split a list of typed expressions into ([TEData], [TEGlobLet])
splitProgram :: Program -> ([TypedExpr], [TypedExpr])
splitProgram []                             = ([], [])
splitProgram (gl@(TEGlobLet _ _ _ _) : tes) = (fst $ splitProgram tes, gl : (snd $ splitProgram tes))
splitProgram (dt@(TEData _ _)        : tes) = (dt : (fst $ splitProgram tes), snd $ splitProgram tes)
splitProgram (_                      : tes) = splitProgram tes

-- Size terms

data Size =
    Min                    -- Minimal value, e.g. Z for Nat and Nil for List
  | NotMin Size
  | D Size                 -- Destructor. D (Param "x") < Param "x"
  | Param Sym              -- Function parameter
  | Var Sym                -- Non-parameter value
  | C Size                 -- Constructor application. C (Param "x") > Param "x"
  | Unknown                -- When the size is unknown
  | Multiple [Size]        -- Non-deterministic choice. Used when a term can have several possible sizes.
  | Deferred TypedExpr
  deriving (Eq, Show)

type Alias = (Size, Size)
withAlias :: Size -> Alias -> Size
withAlias Min       (Min, s)     = s
withAlias (NotMin s) (NotMin s', s'') = if s == s' then s'' else NotMin (s `withAlias` (NotMin s', s'')) 
withAlias (D s)     (D s', s'')  = s `withAlias` (s', s'')
withAlias (Param x) (Param y, s) = if x == y then s else Param x
withAlias (Var x)   (Var y, s)   = if x == y then s else Var x
withAlias (C s)     (C s', s'')  = s `withAlias` (s', s'')
withAlias (Multiple ss) (s, s')  = Multiple $ map (\t -> t `withAlias` (s, s')) ss
withAlias s _ = s

reduceSize :: Size -> Size
reduceSize Min           = Min
reduceSize (NotMin s)    = NotMin (reduceSize s)
reduceSize (D (C s))     = reduceSize s
reduceSize (D s)         = case (reduceSize s) of
                             Min -> Min
                             s'   -> D s'
reduceSize (Param x)     = Param x
reduceSize (Var x)       = Var x
reduceSize (C (D s))     = reduceSize s
reduceSize (C s)         = C (reduceSize s)
reduceSize Unknown       = Unknown
reduceSize (Multiple ss) = Multiple $ map reduceSize ss
reduceSize (Deferred e)  = Deferred e

instance Ord Size where -- TODO: Compare skal give mening!
  compare x y = compare' (reduceSize x) (reduceSize y)
    where
      -- Min
      compare' Min Min = EQ
      compare' Min (NotMin _) = LT
      compare' Min (C _) = LT
      compare' Min (D s) = case s of
                             Min -> EQ
                             _   -> LT
      compare' Min (Param _) = EQ
      compare' Min (Var _) = EQ
      -- NotMin
      compare' (NotMin s) Min = GT
      compare' (NotMin s) (NotMin s') = compare' s s'
      compare' (NotMin s) (C s') = case s' of
                                    Min -> compare' (D s) Min
                                    _ -> compare' s (C s')
      compare' (NotMin s) (D s') = case s' of
                                    Min -> GT
                                    _ -> compare' s (D s')                           
      compare' (NotMin s) (Param x) = compare' s (Param x)
      compare' (NotMin s) (Var x)   = compare' s (Var x)
      -- D
      compare' (D s) Min = case s of
                             Min -> EQ
                             _   -> GT
      compare' (D s) (NotMin s') = case s of
                                     Min -> LT
                                     _   -> compare' (D s) s'
      compare' (D _) (C _)      = LT
      compare' (D s) (D s')       = compare' s s'
      compare' (D _) (Param _)   = LT
      compare' (D _) (Var _)     = LT
      -- Param
      compare' (Param _) Min     = GT
      compare' (Param x) (NotMin s) = compare' (Param x) s
      compare' (Param _) (C _)   = LT
      compare' (Param _) (D _)   = GT
      compare' (Param x) (Param y) = if x == y then EQ else GT
      compare' (Param _) (Var _) = EQ
      -- Var
      compare' (Var _) Min     = GT
      compare' (Var x) (NotMin s) = compare' (Var x) s
      compare' (Var _) (C _)   = LT
      compare' (Var _) (D _)   = GT
      compare' (Var _) (Param _) = EQ
      compare' (Var x) (Var y) = if x == y then EQ else GT
      -- C
      compare' (C _) Min         = GT
      compare' (C s) (NotMin s') = case s of
                                     Min -> compare' Min (D s)
                                     _   -> compare' (C s) s'
      compare' (C s) (C s')      = compare' s s'
      compare' (C s) (D s')      = GT
      compare' (C _) (Param _)   = GT
      compare' (C _) (Var _)     = GT
      -- Unknown
      compare' Unknown   Unknown    = EQ
      compare' _         Unknown    = LT
      -- Multiple
      compare' (Multiple ss) s'     = foldl1 compare (map (\s'' -> compare' s'' s') ss)
      compare' s     (Multiple ss') = foldl1 compare (map (compare' s) ss')
      -- Catch-all
      compare' _ _ = GT
      
      
  
  -- Min
  -- compare Min       Min        = EQ
  -- compare Min       (D Min)    = EQ
  -- compare Min       (Param x)  = EQ
  -- compare Min       (Var x)    = EQ
  -- compare Min       _          = LT
  -- -- Destructors
  -- compare (D s)     (D s')     = compare s s'
  -- compare (D (C s)) s'         = compare s s'
  -- compare s         (D (C s')) = compare s s'
  -- compare (D Min)   Min        = EQ
  -- compare (D s)    (NotMin s') = compare (D s) s'
  -- compare (D s)     _          = LT
  -- -- Param
  -- compare (Param x) (Param y)  = if x == y then EQ else GT
  -- compare (Param x) (Var y)    = EQ
  -- compare (Param x) Min        = EQ
  -- compare (Param x) (D s)      = GT
  -- compare (Param x) (NotMin s) = compare (Param x) s
  -- compare (Param x) _          = LT
  -- -- Var
  -- compare (Var x)   (Var y)    = if x == y then EQ else GT
  -- compare (Var x)   (Param y)  = EQ
  -- compare (Var x)   Min        = EQ
  -- compare (Var x)   (D s)      = GT
  -- compare (Var x)   (NotMin s) = compare (Var x) s
  -- compare (Var x)   _          = LT
  -- -- Constructors
  -- compare (C s)     (C s')     = compare s s'
  -- compare (C (D s)) s'         = compare s s'
  -- compare s         (C (D s')) = compare s s'
  -- compare (C s)     Min        = GT
  -- compare (C s)     (D s')     = if s == s' then GT else compare s s'
  -- compare (C s)     (Param x)  = GT
  -- compare (C s)     (Var x)    = GT
  -- compare (C s)    (NotMin s') = compare (C s) s'
  -- compare (C s)     _          = LT
  -- -- NotMin
  -- compare (NotMin s) Min       = GT
  -- compare (NotMin s) s'        = compare s s'
  -- -- Unknown
  -- compare Unknown   Unknown    = EQ
  -- compare _         Unknown    = LT
  -- -- Multiple
  -- compare (Multiple ss) s'     = foldl1 compare (map (\s'' -> compare s'' s') ss)
  -- compare s     (Multiple ss') = foldl1 compare (map (compare s) ss')
  -- -- Catch-all
  -- compare _         _          = EQ

  
-- Control-flow graphs

-- Control points represent the terms that must terminate
-- class ControlPoint c where
--   identifier    :: c a -> String
--   dataPositions :: c a -> [DataPosition b]
  
data ControlPoint a =
    Global Sym a
  | Local Sym (ControlPoint a) a deriving (Show)

instance Eq (ControlPoint a) where
  f == g = controlPointId f == controlPointId g

instance Ord (ControlPoint a) where
  compare f g = compare (controlPointId f) (controlPointId g)

-- A Call is a connection between two control points, establishing interdependency
type Substitution a = [(Sym, DataPosition a)]
type Call a b = (ControlPoint a, b, ControlPoint a)
type CallSequence a b = [Call a b]

transitiveCall :: Call a b -> Call a b -> Maybe (CallSequence a b)
transitiveCall x y = Nothing -- TODO

isRecursiveTransitive :: CallSequence a b -> Bool
isRecursiveTransitive x = False -- TODO

isReachable :: Call a b -> Bool -- Is the call reachable from the main function
isReachable x = False

-- type ControlFlowGraph a b = [Call a b]

controlPointId :: ControlPoint a -> Sym
controlPointId (Global id _) = id
controlPointId (Local id _ _) = id

controlPointData :: ControlPoint a -> a
controlPointData (Global _ a)  = a
controlPointData (Local _ _ a) = a


-- Size-change graphs

data Arrow = Descending | NonIncreasing deriving (Eq, Show)

-- Data positions represent the terms that (may) change size
newtype DataPosition a = DataPos { getData :: a } deriving Eq

instance Show a => Show (DataPosition a) where
  show dpos = show (getData dpos)

-- A size-change arc describes a change between two data positions
type SCArc a = (DataPosition a, Arrow, DataPosition a)

-- A size-change graph is a set of size-change arcs.
type SizeChangeGraph a b = (ControlPoint a, [SCArc b], ControlPoint a)

type Multipath a b = [SizeChangeGraph a b]

type Thread a = [SCArc a]

-- Functions on size-change graphs

hasArc :: Eq b => SizeChangeGraph a b -> SCArc b -> Bool
hasArc (_, arcs, _) arc = any (== arc) arcs

isArcSafe :: Ord b => SizeChangeGraph a b -> Bool
isArcSafe (as, arcs, bs) = all (\arc -> isSafeArc arc) arcs && hasConsistentArcs arcs
 where
   isSafeArc :: Ord b => SCArc b -> Bool
   isSafeArc (DataPos a, Descending, DataPos b)    = a < b
   isSafeArc (DataPos a, NonIncreasing, DataPos b) = a <= b

   hasConsistentArcs :: Eq a => [SCArc a] -> Bool -- Consistency = no duplicate arcs with different arrows
   hasConsistentArcs arcs = null $ [ (a, y) | (a, arr, b) <- arcs, (x, arr', y) <- arcs, a == x, b == y, not (arr == arr') ]

areComposable :: Eq a => SizeChangeGraph a b -> SizeChangeGraph a b -> Bool
areComposable (_, _, y) (y', _, _) = y == y'

-- compose :: (Eq a, Eq b) => SizeChangeGraph a b -> SizeChangeGraph a b -> Maybe (SizeChangeGraph a b)
-- compose g@(x, xy, y) g'@(y', yz, z)
--   | areComposable g g' = Just (x, composeArrows xy yz, z)
--   | otherwise          = Nothing
--   where
--     composeArrows :: Eq a => [SCArc a] -> [SCArc a] -> [SCArc a]
--     composeArrows xy yz =
--           [ (x, NonIncreasing   , z) | (x, arr, y) <- xy, (y', arr', z) <- yz ]
          -- [ (x, Descending   , z) | (x, arr, y) <- xy, (y', arr', z) <- yz, y == y',
          --                           arr == Descending || arr' == Descending       ] ++
          -- [ (x, NonIncreasing, z) | (x, arr, y) <- xy, (y', arr', z) <- yz, y == y',
          --                           arr == NonIncreasing && arr' == NonIncreasing ]

-- composeAll :: (Eq a, Eq b) => SizeChangeGraph a b -> [SizeChangeGraph a b] -> [SizeChangeGraph a b]
-- composeAll g [] = [g]
-- composeAll g gs = mapMaybe (compose g) gs

compose :: Eq a => SizeChangeGraph a (Sym, Size) -> SizeChangeGraph a (Sym, Size) -> Maybe (SizeChangeGraph a (Sym, Size))
compose g@(x, xy, y) g'@(y', yz, z)
  | areComposable g g' = Just (x, composeArrows xy yz, z)
  | otherwise          = Nothing
  where
    composeArrows :: [SCArc (Sym, Size)] -> [SCArc (Sym, Size)] -> [SCArc (Sym, Size)]
    composeArrows xy yz =
          [ (DataPos (x,xs), Descending, DataPos (z,zs)) |
              (DataPos (x,xs), arr, DataPos (y,_)) <- xy, (DataPos (y',_), arr', DataPos (z,zs)) <- yz, y == y',
              arr == Descending || arr' == Descending       ] ++
          [ (DataPos (x,xs), NonIncreasing, DataPos (z,zs)) |
              (DataPos (x,xs), arr, DataPos (y,_)) <- xy, (DataPos (y',_), arr', DataPos (z,zs)) <- yz, y == y',
              arr == NonIncreasing && arr' == NonIncreasing ]



cyclicMultipaths :: Eq a => [SizeChangeGraph a b] -> [Multipath a b]
cyclicMultipaths []                 = []
cyclicMultipaths (scgs@((f,_,g):_)) = cycles f (assocListFromTriples scgs) [] []
  where            -- Current node      Adjacency list                               Path
    cycles :: Eq a => ControlPoint a -> [(ControlPoint a, [SizeChangeGraph a b])] -> [SizeChangeGraph a b] ->
             -- Visited          Cycles
             [ControlPoint a] -> [Multipath a b]
    cycles node graph path visited =
      let backtracking = node `elem` visited
          nodesVisited = if not backtracking then node : visited else visited
          nodeEdges = case lookup node graph of
                        Just edges -> edges
                        Nothing    -> []
          -- cycleEdges create a cycle
--          (cycleEdges, unexploredEdges) = partition (\(f, _, g) -> g `elem` nodesVisited) nodeEdges
          (cycleEdges, otherEdges) = partition (\(f,_,g) -> let inPath = any (\(m,_,n) -> g == m) path
                                                            in if backtracking
                                                               then inPath 
                                                               else inPath || g `elem` nodesVisited) nodeEdges
          unexploredEdges = filter (\(f, _, g) -> g `notElem` nodesVisited) otherEdges
          cyclePaths = map (\(f,x,g) -> (subListFrom (\(m,_,n) -> g == m) path) ++ [(f,x,g)]) cycleEdges
          unexploredPaths =
            case unexploredEdges of
              [] -> case path of
                      -- Find out if any nodes have not been considered
                      [] -> case find (\(n, _) -> n `notElem` nodesVisited) graph of
                              Just (n, _) -> cycles n graph [] [] -- Found one!
                              Nothing     -> [] -- All nodes have been considered, terminate
                      ((f,_,_):p) -> cycles f graph p nodesVisited -- Backtrack
              unexplored ->
                concat $ map (\(f,x,g) -> cycles g graph (path ++ [(f,x,g)]) nodesVisited) unexplored 
       in cyclePaths ++ unexploredPaths

cycledUntilHead :: Eq a => [a] -> a -> [a]
cycledUntilHead (x:xs) y
  | y `elem` (x:xs) = if x == y then (x:xs) else cycledUntilHead (xs ++ [x]) y
  | otherwise       = (x:xs)

allMultipaths :: (Eq a, Eq b) => Multipath a b -> [Multipath a b]
allMultipaths multipath = map (\scg -> cycledUntilHead multipath scg) multipath

collapse :: Eq a => Multipath a (Sym, Size) -> Maybe (SizeChangeGraph a (Sym, Size))
collapse multipath
  | not (null multipath) = foldM compose (head multipath) (tail multipath)
  | otherwise            = Nothing                           


-- Functions for determining termination

isLoop :: Eq a => SizeChangeGraph a b -> Bool
isLoop (f, _, g) = f == g

-- | Determines whether a size-change graph G is equal to G composed with G (i.e. G;G)
isSelfComposition :: Eq a => SizeChangeGraph a (Sym, Size) -> Bool
isSelfComposition g = case g `compose` g of
                        Just g' -> g == g'
                        Nothing -> False

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
globalControlPoints [] = []
globalControlPoints (TEGlobLet ty name params body : globs) =
  (Global name (paramsAsData params), body) : globalControlPoints globs
globalControlPoints (_ : globs) = globalControlPoints globs

data ParameterType = Recursive | NonRecursive deriving Eq

data Constructor = Constructor { constructorName :: Sym,
                                 constructorParameters :: [ParameterType] }

globalDataConstructors :: [TypedExpr] -> [Constructor]
globalDataConstructors [] = []
globalDataConstructors ((TEData ty@(TRecInd _ (TVari constructors)) _):ds) =
  let name = fst
      parameterTypes = map (\t -> if t == ty then Recursive else NonRecursive)
  in map (\(name,params) -> Constructor name (parameterTypes params)) constructors
     ++ globalDataConstructors ds
globalDataConstructors (_:ds) = globalDataConstructors ds

-- dataEnv :: ControlPoint DataEnv -> DataEnv
-- dataEnv (Global _ env)  = env
-- dataEnv (Local _ parent env) = env ++ dataEnv parent

-- If no local dataenv, then control point is value

controlPointFromExpr :: TypedExpr -> [ControlPoint a] -> Maybe (ControlPoint a)
controlPointFromExpr (TEVar _ f) cps = find (\cp -> f == controlPointId cp) cps
controlPointFromExpr _           _   = Nothing

constructorFromExpr :: TypedExpr -> [Constructor] -> Maybe (Constructor)
constructorFromExpr (TEVar _ f) constrs = find (\c -> f == constructorName c) constrs
constructorFromExpr _           _       = Nothing


data CallGraphEnv = CallGraphEnv { controlPoints :: [ControlPoint DataEnv],
                                   constructors  :: [Constructor],
                                   dataPositions :: DataEnv,
                                   hints         :: Hints }

updateControlPoint :: ControlPoint DataEnv -> Size -> (Size -> Size) -> ControlPoint DataEnv
updateControlPoint (Global name params)       size f = Global name (updateDataEnv params size f)
updateControlPoint (Local name parent params) size f = Local name parent (updateDataEnv params size f)

updateDataEnv :: DataEnv -> Size -> (Size -> Size) -> DataEnv
updateDataEnv [] size f = []
updateDataEnv ((name, DataPos s):sizes) size f = if s == size
                                                 then (name, DataPos $ f s) : updateDataEnv sizes size f
                                                 else (name, DataPos s) : updateDataEnv sizes size f
-- updateDataEnv params size f =
--   map (\(p, DataPos s) -> if size == s then (p, DataPos s) else (p, DataPos s)) params


addControlPoint :: ControlPoint DataEnv -> CallGraphEnv -> CallGraphEnv
addControlPoint cp (CallGraphEnv cps cos dpos hs) = CallGraphEnv (cp:cps) cos dpos hs

addData :: DataEnv -> CallGraphEnv -> CallGraphEnv
addData d (CallGraphEnv cps cos dpos hs) = CallGraphEnv cps cos (d ++ dpos) hs

addHints :: Hints -> CallGraphEnv -> CallGraphEnv
addHints h (CallGraphEnv cps cos dpos hs) = CallGraphEnv cps cos dpos (h ++ hs)

getVariantType :: Type -> ErrorT CallGraphError Identity [(Sym, [Type])]
getVariantType (TVari ts)             = return ts
getVariantType (TRecInd _ (TVari ts)) = return ts
getVariantType _                      = throwError $ CallGraphError "Matched expression does not have a variant type"

type CallGraphError = NonTermination

type WithCallGraphEnv m a = ReaderT CallGraphEnv m a

type CallGraph = WithCallGraphEnv (ErrorT CallGraphError Identity) [Call DataEnv (Substitution Size)]

runCallGraph cp expr env = runIdentity (runErrorT $ runReaderT (callGraph' cp expr) env)

callGraph' :: ControlPoint DataEnv -> TypedExpr -> CallGraph
callGraph' f (TEApp _ (TEFold _ _) [tag@(TETag _ _ _)]) = callGraph' f tag
callGraph' f (TEApp _ (TEUnfold _ _) [arg])             = callGraph' f arg
callGraph' f (TEApp _ g args)                           = do
  env <- ask
  case controlPointFromExpr g (controlPoints env) of -- Is g a function?
    Just target -> do
      let targetData cp = map fst $ controlPointData cp
      let call h argd = (f, zip (targetData h) argd, h)
      argGraphs <- mapM (callGraph' f) args
      argData <- mapM (sizeOf' f) args
      let argPositions = map DataPos argData
      return $ call target argPositions : (concat argGraphs)
    Nothing ->
      case constructorFromExpr g (constructors env) of -- Is g a data constructor?
        Just _  -> do argGraphs <- mapM (callGraph' f) args
                      return $ concat argGraphs
        Nothing ->
          throwError $
           CallGraphError "Called function does not exist. This is a type checking issue."
callGraph' f (TELet ty id exprty params expr body)      = do
  let paramData = paramsAsData params
  let localDef = Local id f paramData
  let exprEnv = addData paramData . addControlPoint localDef
  exprGraph <- local exprEnv $ callGraph' localDef expr
  exprSize <- local exprEnv $ sizeOf' f expr
  case exprGraph of
    [] -> case params of
            Just _ -> 
              let env = addData [(id, DataPos $ Deferred expr)] .
                        addControlPoint localDef
              in local env $ callGraph' f body
            Nothing ->
              let env = addData [(id, DataPos exprSize)]
              in local env $ callGraph' f body
    eg -> do
      bodyGraph <- local (addControlPoint localDef) $ callGraph' f body
      return $ eg ++ bodyGraph
callGraph' f (TECase ty expr cases)                     = do
  env <- ask
  exprSize <- sizeOf' f expr
  let exprType = getTypeAnno expr
  let isRecType = (== exprType)
  variant <- lift $ getVariantType exprType
  caseGraphs <- forM cases $ \(id, (vars, caseExpr)) -> do
                  caseTypes <- case lookup id variant of
                                 Just ts -> return ts
                                 Nothing -> throwError $ CallGraphError "Incompatible pattern"
                  let annoVars = zip vars caseTypes
                  let argEnv = map (\(v, t) -> if isRecType t
                                               then (v, DataPos $ D exprSize)
                                               else (v, DataPos $ Var v)) annoVars
                  let isBaseCase = all (\(v,t) -> not $ isRecType t) annoVars
                  if isBaseCase
                  then let newF = updateControlPoint f exprSize (const Min)
                           caseEnv = addData argEnv . addHints [(expr, id)] . addControlPoint newF .
                                     addData (map (\(name, size) -> (name, DataPos Min)) $ filter (\(_, DataPos size) -> size == exprSize) (dataPositions env))
                       in local caseEnv $ callGraph' newF caseExpr
                  else let newF = updateControlPoint f exprSize NotMin
                           caseEnv = addData argEnv . addHints [(expr, id)] . addControlPoint newF .
                                     addData (map (\(name, DataPos size) -> (name, DataPos $ NotMin size)) $ filter (\(_, DataPos size) -> size == exprSize) (dataPositions env))
                       in local caseEnv $ callGraph' newF caseExpr
  return $ concat caseGraphs
callGraph' f (TETag ty id args)                          = do
  argGraphs <- mapM (callGraph' f) args
  return $ concat argGraphs
callGraph' f@(Global id dataenv) (TEGlobLet _ id' _ body)
  | id == id' = callGraph' f body
  | otherwise =
     throwError $ CallGraphError "Attempt to generate call graph for mismatching control point and definition."
callGraph' _ _                                           = return []

type SizeError = CallGraphError
type ExprSize = WithCallGraphEnv (ErrorT SizeError Identity) Size

sizeOf' :: ControlPoint DataEnv -> TypedExpr -> ExprSize
sizeOf' f (TEVar _ id)                              = do
  env <- ask
  case lookup id (dataPositions env) of
    Just (DataPos (Deferred e)) -> sizeOf' f e
    Just (DataPos s)            -> return s
    Nothing                     ->
      case find (\entry -> constructorName entry == id) (constructors env) of
        Just (Constructor _ []) -> return Min
        _                       -> return Unknown
sizeOf' f (TEApp _ (TEFold _ _) [tag@(TETag _ _ _)]) = sizeOf' f tag
sizeOf' f (TEApp _ (TEUnfold _ _) [arg])             = sizeOf' f arg
sizeOf' cp (TEApp _ f args) = do
  env <- ask
  case controlPointFromExpr f (controlPoints env) of
    Just target -> do
      let targetData = controlPointData target
      argSizes <- mapM (sizeOf' cp) args
      let argEnv = map DataPos argSizes
      local (addData $ zip (map fst targetData) argEnv) $ sizeOf' cp f
    Nothing ->
      case constructorFromExpr f (constructors env) of
        Just constructor ->
          let argTypes = zip args (constructorParameters constructor)
              (nonRecArg, recArgs) = partition (\(e,t) -> t == NonRecursive) argTypes
          in case recArgs of
               []         -> return Min
               [(arg, _)] -> do size <- sizeOf' cp arg; return $ C size
               args       -> do sizes <- mapM (sizeOf' cp) (map fst recArgs)
                                return (Multiple $ map C sizes)
        Nothing -> throwError $ SizeError "Called function does not exist. This is a type checking issue."
sizeOf' f (TELet _ id _ p expr body)                = do
  let params = paramsAsData p
  let localDef = Local id f params
  let localEnv = addControlPoint localDef . addData params
  exprSize <- local localEnv $ sizeOf' localDef expr
  local (addData [(id, DataPos exprSize)]) $ sizeOf' f body
sizeOf' f (TECase ty expr cases)                    = do
  env <- ask
  exprSize <- sizeOf' f expr
  let exprType = getTypeAnno expr
  let isRecType = (== exprType)
  variant <- lift $ getVariantType exprType
  casesWSize <- forM cases $ \(id, (vars, caseExpr)) -> do
                 caseTypes <- case lookup id variant of
                                Just ts -> return ts
                                Nothing  ->
                                  throwError $ SizeError "Incompatible pattern"
                 let annoVars = zip vars caseTypes
                 let argEnv = map (\(v, t) -> if isRecType t
                                              then (v, DataPos $ D exprSize)
                                              else (v, DataPos $ Var v)) annoVars
                 let isBaseCase = all (\(v,t) -> not $ isRecType t) annoVars
                 if isBaseCase
                  then do let newF = updateControlPoint f exprSize (const Min)
                          let caseEnv = addData argEnv . addControlPoint newF .
                                        addData (map (\(name, DataPos size) -> (name, DataPos Min)) $ filter (\(_, DataPos size) -> size == exprSize) (dataPositions env))
                          baseCaseSize <- local caseEnv $ sizeOf' newF caseExpr
                          return (id, baseCaseSize)
                  else do let newF = updateControlPoint f exprSize NotMin
                          let caseEnv = addData argEnv . addControlPoint newF .
                                        addData (map (\(name, DataPos size) -> (name, DataPos $ NotMin size)) $ filter (\(_, DataPos size) -> size == exprSize) (dataPositions env))
                          size <- local caseEnv $ sizeOf' newF caseExpr
                          return (id, size)
  let caseSizes = map snd casesWSize
  let maxSize = if null caseSizes then Unknown else foldr1 max caseSizes -- Gør det mest konservative.
  case lookup expr (hints env) of
    Just hint ->
      case find (\c -> fst c == hint) casesWSize of
        Just (_, size) -> return size
        Nothing        -> return maxSize
    Nothing -> return maxSize
sizeOf' f (TETag tagty id args)                     =
  let hasTaggedType arg = case getTypeAnno arg of
                            vari@(TVari _) -> vari == tagty
                            TRecInd _ vari    -> vari == tagty
                            _              -> False
      sizeChangingArgs = filter hasTaggedType args
  in case sizeChangingArgs of
       []    -> return Min
       [arg] -> do size <- sizeOf' f arg; return $ C size
       args  -> do sizes <- mapM (sizeOf' f) args
                   return (Multiple $ map C sizes)
sizeOf' _ _ = return Unknown

sizeChangeGraph :: Call DataEnv (Substitution Size) -> SizeChangeGraph DataEnv (Sym, Size)
sizeChangeGraph (f, subs, g) = (f, mapMaybe toSCArc subs, g)
  where
    toSCArcs :: [(Sym, DataPosition Size)] -> [(SCArc (Sym, Size))]
    toSCArcs subs =
      let fData = controlPointData f
          subRoots = map (\(x, DataPos size) -> (x, DataPos size, parameterRoots size)) subs
          (paramSizes, otherSizes) = partition (\(_,_,roots) -> not $ null roots) subRoots
          paramfRoots = map (\(x,size,roots) -> (x,size,filter (\(y,_) -> y `elem` roots) fData)) paramSizes
          orders = mapMaybe (\(x,DataPos size,fs) -> minOrder (comparisons size fs) Nothing) paramfRoots
          comparisons argSize l =
            map (\(x, DataPos xSize) -> (x, DataPos xSize, compare argSize xSize)) l
      in []
          -- (x, DataPos initSize, ord) <- minOrder (if null $ comparisons fRoots
          --                                           then comparisons fData
          --                                           else comparisons fRoots)
          --                                 Nothing
          --   case ord of
          --     LT -> Just (DataPos (x, initSize), Descending, DataPos (y, argSize))
          --     EQ -> Just (DataPos (x, initSize), NonIncreasing, DataPos (y, argSize))
          --     GT -> Nothing

          -- comparisons = map (\(x, y) ->
          --                     let x' = fst x
          --                         y' = fst y
          --                         xSize = getData $ snd x
          --                         ySize = getData $ snd y
          --                     in
          --                     (DataPos (x', xSize), compare xSize ySize, DataPos (y', ySize))) argMap
      -- in [ (x, Descending, y)    | (x, cmp, y) <- comparisons, cmp == LT ] ++
      --    [ (x, NonIncreasing, y) | (x, cmp, y) <- comparisons, cmp == EQ ]

    toSCArc :: (Sym, DataPosition Size) -> Maybe (SCArc (Sym, Size))
    toSCArc (y, arg) = do
      let fData = controlPointData f
      let argSize = getData arg
      let roots = filter (\(x,_) -> x `elem` parameterRoots argSize) fData
      let comparisons =
            map (\(x, DataPos xSize) -> (x, DataPos xSize, compare argSize xSize)) $ roots
            --if null roots then fData else roots
      (x, DataPos initSize, ord) <- minOrder comparisons Nothing
      case ord of
        LT -> Just (DataPos (x, initSize), Descending, DataPos (y, argSize))
        EQ -> Just (DataPos (x, initSize), NonIncreasing, DataPos (y, argSize))
        GT -> Nothing
      
--       let argSize = getData arg
-- --          argRoots = parameterRoots argSize
--           fParams = mapMaybe (\p -> find (\(x, _) -> p == x) (controlPointData f)) argSize -- argRoots
--           orderedParams = map (\(x, DataPos xSize) -> (x, DataPos xSize, compare argSize xSize)) fParams
--       in do
--            (x, DataPos initSize, ord) <- minOrder orderedParams Nothing
--            arc <- case ord of
--                     LT -> Just (DataPos (x, initSize), Descending, DataPos (y, argSize))
--                     EQ -> Just (DataPos (x, initSize), NonIncreasing, DataPos (y, argSize))
--                     GT -> Nothing
--            return arc
           
    parameterRoots :: Size -> [Sym]
    parameterRoots (Param x)     = [x]
    parameterRoots (D s)         = parameterRoots s
    parameterRoots (C s)         = parameterRoots s
    parameterRoots (NotMin s)    = parameterRoots s
    parameterRoots (Multiple ss) = concat $ map parameterRoots ss
    parameterRoots _             = []

    minOrder :: Ord c => [(a, b, c)] -> Maybe (a, b, c) -> Maybe (a, b, c)
    minOrder []                     acc                     = acc
    minOrder (el@(_, _, ord) : xs)  Nothing                 = minOrder xs (Just el)
    minOrder (new@(_, _, ord) : xs) old@(Just (_, _, ord')) = if ord < ord' 
                                                              then minOrder xs (Just new)
                                                              else minOrder xs old

identityArcs :: SizeChangeGraph DataEnv (Sym, Size) -> [SCArc (Sym, Size)]
identityArcs scg@(f, arcs, g)
  | isLoop scg = [ (DataPos (a, s), arc, DataPos (b, s')) | (DataPos (a, s), arc, DataPos (b, s')) <- arcs, a == b ]
  | otherwise  = []

descendingArcs :: [SCArc a] -> [SCArc a]
descendingArcs arcs = filter (\(f, arr, g) -> arr == Descending) arcs

hasDescendingArcs :: SizeChangeGraph a b -> Bool
hasDescendingArcs (f, arcs, g) = not (null $ descendingArcs arcs)

showSizeChangeGraph :: SizeChangeGraph DataEnv (Sym, Size) -> Bool -> String
showSizeChangeGraph (f, arcs, g) True  = controlPointId f ++ " " ++ showArcs arcs ++ " " ++ controlPointId g
  where
    showArcs :: [SCArc (Sym, Size)] -> String
    showArcs arcs = "[" ++ intercalate "," (map show arcs) ++ "]"
showSizeChangeGraph (f, arcs, g) False = controlPointId f ++ " --> " ++ controlPointId g    

showMultipath :: Multipath DataEnv (Sym, Size) -> Bool -> String
showMultipath mp withArcs = intercalate " --> " $ map (\scg -> "(" ++ showSizeChangeGraph scg withArcs ++ ")") mp
    
data Termination = Termination [SizeChangeGraph DataEnv (Sym, Size)]

instance Show Termination where
  show (Termination scgs) =
    let showF (f,arcs,g) = controlPointId f ++ " terminates on input " ++ (show $ (map show (descendingArcs arcs)))
    in (intercalate "\n" $ map showF scgs)

data NonTermination =
    UnsafeMultipathError (Multipath DataEnv (Sym, Size))
  | InfiniteRecursion (Multipath DataEnv (Sym, Size))
  | UnknownCause String
  | CallGraphError String
  | SizeError String

instance Show NonTermination where
  show (UnsafeMultipathError mp) = "Could not determine termination due to unsafe multipath: "
                                   ++ showMultipath mp False
  show (InfiniteRecursion mp)    = "Program is not size-change terminating due to possible infinite recursion in call chain: "
                                   ++ showMultipath mp True
  show (UnknownCause msg)        = show msg
  show (CallGraphError msg)      = "Error while building the call graph: " ++ msg
  show (SizeError msg)           = "Error while determining size of expression: " ++ msg

instance Error NonTermination

-- Theorem 4!
isSizeChangeTerminating :: Program -> Either NonTermination Termination
isSizeChangeTerminating []   = return $ Termination []
isSizeChangeTerminating prog = do
  let (dataExprs, funExprs) = splitProgram prog
  let globalFuns = globalControlPoints funExprs
  let globalConstrs = globalDataConstructors dataExprs
  let initEnv cp = CallGraphEnv (map fst globalFuns) globalConstrs (controlPointData cp) []
  callGraphs <- mapM (\(cp, e) -> runCallGraph cp e (initEnv cp)) globalFuns
  let calls = concat callGraphs
  let sizeChangeGraphs = map sizeChangeGraph calls
  let multipaths = concat $ map allMultipaths (cyclicMultipaths sizeChangeGraphs)
  let collapsedMultipaths = map (\mp -> (mp, collapse mp)) multipaths
  let unsafeMultipaths = map fst $ filter (\(mp, collapsed) -> isNothing collapsed) collapsedMultipaths
  let safeCollapsedMultipaths = map (\(mp, c) -> (mp, fromJust c)) $ [ (m, c) | (m, c) <- collapsedMultipaths, isJust c ]
  let possiblyNonTerminating =
        filter (\(mp, collapsed) -> isLoop collapsed && isSelfComposition collapsed) safeCollapsedMultipaths
  let descendingArcsWithGraph m = map (\(mp, collapsed) -> (mp, descendingArcs (identityArcs collapsed))) m
  let graphsWithNoDescendingArcs m = filter (\(mp, arcs) -> null arcs) (descendingArcsWithGraph m)
  case unsafeMultipaths of
    [] -> case graphsWithNoDescendingArcs possiblyNonTerminating of
            []            -> return $ Termination (map snd safeCollapsedMultipaths)
                             --throwError $ UnknownCause $ concat $ map (\s -> showSizeChangeGraph s True) (map snd safeCollapsedMultipaths)
                             -- throwError $ UnknownCause $ concat $ map (\s -> showMultipath s False) (map fst safeCollapsedMultipaths)
                             --throwError $ UnknownCause $ show calls
                             -- throwError $ UnknownCause $ (show calls) ++ "\n" ++ (intercalate ", " $ map (\s -> showSizeChangeGraph s True) sizeChangeGraphs)
                             -- throwError $ UnknownCause $ show possiblyNonTerminating
            nonDescending -> throwError $
                               InfiniteRecursion (head $ map fst nonDescending)
                              -- UnknownCause $ show (descendingArcsWithGraph possiblyNonTerminating)
                               -- UnknownCause (show calls)
                               --UnknownCause $ (intercalate ", " $ map (\s -> showSizeChangeGraph s True) $ map snd safeCollapsedMultipaths)
                               --UnknownCause $ show $ map (\m -> showMultipath m False) multipaths
    unsafe -> throwError $ UnsafeMultipathError (head unsafe)

