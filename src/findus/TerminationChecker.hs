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
assocListFromTriples :: Eq a => [(a, b, c)] -> [(a, [(a, b, c)])]
assocListFromTriples [] = []
assocListFromTriples xs =
  let groups = groupBy (\(a,_,c) -> \(d,_,e) -> a == d) xs
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
withAlias (D s)     (D s', s'')  = s `withAlias` (s', s'')
withAlias (Param x) (Param y, s) = if x == y then s else Param x
withAlias (Var x)   (Var y, s)   = if x == y then s else Var x
withAlias (C s)     (C s', s'')  = s `withAlias` (s', s'')
withAlias (Multiple ss) (s, s')  = Multiple $ map (\t -> t `withAlias` (s, s')) ss
withAlias s _ = s

instance Ord Size where -- TODO: Compare skal give mening!
  -- Min
  compare Min       Min        = EQ
  compare Min       (D Min)    = EQ
  compare Min       (Param x)  = EQ
  compare Min       (Var x)    = EQ
  compare Min       _          = LT
  -- Destructors
  compare (D s)     (D s')     = compare s s'
  compare (D (C s)) s'         = compare s s'
  compare s         (D (C s')) = compare s s'
  compare (D Min)   Min        = EQ
  compare (D s)     _          = LT
  -- Param
  compare (Param x) (Param y)  = if x == y then EQ else GT
  compare (Param x) (Var y)    = EQ
  compare (Param x) Min        = EQ
  compare (Param x) (D s)      = GT
  compare (Param x) _          = LT
  -- Var
  compare (Var x)   (Var y)    = if x == y then EQ else GT
  compare (Var x)   (Param y)  = EQ
  compare (Var x)   Min        = EQ
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
-- class ControlPoint c where
--   identifier    :: c a -> String
--   dataPositions :: c a -> [DataPosition b]
  
data ControlPoint a =
    Global Sym a
  | Local Sym (ControlPoint a) a deriving (Eq, Show)

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

compose :: (Eq a, Eq b) => SizeChangeGraph a b -> SizeChangeGraph a b -> Maybe (SizeChangeGraph a b)
compose g@(x, xy, y) g'@(y', yz, z)
  | areComposable g g' = Just (x, composeArrows xy yz, z)
  | otherwise          = Nothing
  where
    composeArrows :: Eq a => [SCArc a] -> [SCArc a] -> [SCArc a]
    composeArrows xy yz =
          [ (x, Descending   , z) | (x, arr, y) <- xy, (y', arr', z) <- yz, y == y',
                                    arr == Descending || arr' == Descending       ] ++
          [ (x, NonIncreasing, z) | (x, arr, y) <- xy, (y', arr', z) <- yz, y == y',
                                    arr == NonIncreasing && arr' == NonIncreasing ]

composeAll :: (Eq a, Eq b) => SizeChangeGraph a b -> [SizeChangeGraph a b] -> [SizeChangeGraph a b]
composeAll g [] = [g]
composeAll g gs = mapMaybe (compose g) gs

cyclicMultipaths :: Eq a => [SizeChangeGraph a b] -> [Multipath a b]
cyclicMultipaths []                 = []
cyclicMultipaths (scgs@((f,_,g):_)) = cycles f (assocListFromTriples scgs) [] []
  where            -- Current node      Adjacency list                               Path
    cycles :: Eq a => ControlPoint a -> [(ControlPoint a, [SizeChangeGraph a b])] -> [SizeChangeGraph a b] ->
             -- Visited          Cycles
             [ControlPoint a] -> [Multipath a b]
    cycles node graph path visited =
      let nodesVisited = if node `notElem` visited then node : visited else visited
          nodeEdges = case lookup node graph of
                        Just edges -> edges
                        Nothing    -> []
          -- cycleEdges create a cycle
          (cycleEdges, unexploredEdges) = partition (\(f, _, g) -> g `elem` nodesVisited) nodeEdges
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

collapse :: (Eq a, Eq b) => Multipath a b -> Maybe (SizeChangeGraph a b)
collapse multipath
  | not (null multipath) = foldM compose (head multipath) (tail multipath)
  | otherwise            = Nothing                           


-- Functions for determining termination

isLoop :: Eq a => SizeChangeGraph a b -> Bool
isLoop (f, _, g) = f == g

-- | Determines whether a size-change graph G is equal to G;G G composed with G (i.e. G;G)
isSelfComposition :: (Eq a, Eq b) => SizeChangeGraph a b -> Bool
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

dataEnv :: ControlPoint DataEnv -> DataEnv
dataEnv (Global _ env)  = env
dataEnv (Local _ parent env) = env ++ dataEnv parent

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
              let env = addData [(id, DataPos $ Deferred body)] .
                        addControlPoint localDef
              in local env $ callGraph' f body
            Nothing ->
              let env = addData [(id, DataPos exprSize)]
              in local env $ callGraph' f body
    eg -> do
      bodyGraph <- local (addControlPoint localDef) $ callGraph' f body
      return $ eg ++ bodyGraph
callGraph' f (TECase ty expr cases)                     = do
  exprSize <- sizeOf' f expr
  let exprType = getTypeAnno expr
  let isRecType = (== exprType)
  variant <- lift $ getVariantType exprType
  caseGraphs <- forM cases $ (\(id, (vars, caseExpr)) -> do
                  caseTypes <- case lookup id variant of
                                 Just ts -> return ts
                                 Nothing -> throwError $ CallGraphError "Incompatible pattern"
                  let annoVars = zip vars caseTypes
                  let argEnv = map (\(v, t) -> if isRecType t
                                               then (v, DataPos $ D exprSize)
                                               else (v, DataPos $ Var v)) annoVars
                  let caseEnv = addData argEnv . addHints [(expr, id)]
                  local caseEnv $ callGraph' f caseExpr)
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
      local (addData $ (zip (map fst targetData) argEnv)) $ sizeOf' cp f
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
  caseSizes <- forM cases $ (\(id, (vars, caseExpr)) -> do
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
                  then do baseCaseSize <- local (addData argEnv) $ sizeOf' f caseExpr
                          return $ baseCaseSize `withAlias` (Min, exprSize)
                  else local (addData argEnv) $ sizeOf' f caseExpr)
  let maxSize = if null caseSizes then Unknown else foldr1 max caseSizes -- Gør det mest konservative.
  case lookup expr (hints env) of
    Just hint ->
      case find (\c -> fst c == hint) cases of
        Just c -> sizeOf' f (TECase ty expr [c]) -- Call recursively on only one case
        Nothing -> return maxSize
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
    toSCArc :: (Sym, DataPosition Size) -> Maybe (SCArc (Sym, Size))
    toSCArc (y, arg) =
      let argSize = getData arg
          argRoots = parameterRoots argSize
          fParams = mapMaybe (\p -> find (\(x, _) -> p == x) (controlPointData f)) argRoots
          orderedParams = map (\(x, DataPos xSize) -> (x, DataPos xSize, compare argSize xSize)) fParams
      in do
           (x, DataPos initSize, ord) <- minOrder orderedParams Nothing
           arc <- case ord of
                    LT -> Just (DataPos (x, initSize), Descending, DataPos (y, argSize))
                    EQ -> Just (DataPos (x, initSize), NonIncreasing, DataPos (y, argSize))
                    GT -> Nothing
           return arc
           
    parameterRoots :: Size -> [Sym]
    parameterRoots (Param x)     = [x]
    parameterRoots (D s)         = parameterRoots s
    parameterRoots (C s)         = parameterRoots s
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
  | isLoop scg = [ (a, arc, b) | (a, arc, b) <- arcs, a == b ]
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
    let showF (f,arcs,g) = controlPointId f ++ " terminates on input " ++ (show $ intersperse ", " (map show (descendingArcs arcs)))
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
  let safeCollapsedMultipaths = zip (map fst collapsedMultipaths) (catMaybes $ map snd collapsedMultipaths)
  let possiblyNonTerminating =
        filter (\(mp, collapsed) -> isLoop collapsed && isSelfComposition collapsed) safeCollapsedMultipaths
  let descendingArcsWithGraph m = map (\(mp, collapsed) -> (mp, descendingArcs (identityArcs collapsed))) m
  let graphsWithNoDescendingArcs m = filter (\(mp, arcs) -> null arcs) (descendingArcsWithGraph m)
  case unsafeMultipaths of
    [] -> case graphsWithNoDescendingArcs possiblyNonTerminating of
            []            -> return $ Termination (map snd safeCollapsedMultipaths)
            nonDescending -> throwError $ InfiniteRecursion (head $ map fst nonDescending) -- UnknownCause (show calls) -- (intercalate ", " $ map (\s -> showSizeChangeGraph s True) sizeChangeGraphs) -- InfiniteRecursion (head $ map fst nonDescending)          
    unsafe -> throwError $ UnsafeMultipathError (head unsafe)

