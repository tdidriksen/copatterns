module TerminationChecker where

import Expr
import TypeChecker
import Data.List
import Data.Maybe
import Control.Monad
import Control.Monad.Error

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

type ControlFlowGraph a b = [Call a b]

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


callGraph :: ControlPoint DataEnv -> TypedExpr -> [ControlPoint DataEnv] ->
             [Constructor] -> DataEnv -> Hints -> [Call DataEnv (Substitution Size)]
callGraph f (TEApp _ (TEFold _ _) [tag@(TETag _ _ _)]) cps constrs dataenv hints = callGraph f tag cps constrs dataenv hints
callGraph f (TEApp _ (TEUnfold _ _) [arg]) cps constrs dataenv hints = callGraph f arg cps constrs dataenv hints
callGraph f (TEApp _ g args) cps constrs dataenv hints =
  case controlPointFromExpr g cps of
    Just target ->
      let targetData cp = map fst $ controlPointData cp
          argPositions = map (\arg -> DataPos $ sizeOf arg f cps constrs dataenv hints) args
          call h = (f, zip (targetData h) argPositions, h)
      in call target : (foldl (++) [] $ map (\arg -> callGraph f arg cps constrs dataenv hints) args)
    Nothing ->
      case constructorFromExpr g constrs of
        Just _  -> foldl (++) [] $ map (\arg -> callGraph f arg cps constrs dataenv hints) args
        Nothing -> error "Called function does not exist. This should have been checked by the type checker." 
callGraph f (TELet ty id exprty params expr body) cps constrs dataenv hints =
  let paramData = paramsAsData params
      localDef = Local id f paramData
      exprGraph = callGraph localDef expr (localDef : cps) constrs (paramData ++ dataenv) hints
      exprSize = sizeOf expr f cps constrs (paramData ++ dataenv) hints
  in case exprGraph of
       [] -> case params of
               Just ps -> callGraph f body (localDef : cps) constrs ((id, DataPos $ Deferred body) : dataenv) hints
               Nothing -> callGraph f body cps constrs ((id, DataPos exprSize) : dataenv) hints
       eg -> eg ++ callGraph f body (localDef : cps) constrs dataenv hints
callGraph f (TECase ty expr cases) cps constrs dataenv hints =
  let exprSize = sizeOf expr f cps constrs dataenv hints
      exprType = getTypeAnno expr
      variant = case exprType of
                     TVari ts          -> ts
                     TRecInd _ (TVari ts) -> ts
                     _                 -> error "Matched expression does not have variant type" -- TODO
      caseTypes id = case lookup id variant of
                          Just tys -> tys
                          Nothing  -> error "Incompatible pattern"
      annotatedVars (id, (vars, _)) = zip vars (caseTypes id)
      isRecType = (== exprType)
      argEnv c = map (\(v, t) -> if isRecType t then (v, DataPos $ D exprSize) else (v, DataPos $ Var v)) (annotatedVars c)
      caseExpr = snd . snd
      constructor = fst
      caseGraphs = map (\c -> callGraph f (caseExpr c) cps constrs (argEnv c ++ dataenv) ((expr, constructor c) : hints)) cases
  in foldl (++) [] $ caseGraphs
callGraph f (TETag ty id args) cps constrs dataenv hints = 
  foldl (++) [] $ map (\arg -> callGraph f arg cps constrs dataenv hints) args
callGraph f@(Global id dataenv) (TEGlobLet _ id' _ body) cps constrs [] hints
  | id == id' = callGraph f body cps constrs dataenv hints
  | otherwise = []
callGraph _ _ _ _ _ _ = []


sizeOf :: TypedExpr -> ControlPoint DataEnv -> [ControlPoint DataEnv] ->
          [Constructor] -> DataEnv -> Hints -> Size
sizeOf (TEVar _ id) f cps constrs env hints =
  case lookup id env of
    Just (DataPos (Deferred e)) -> sizeOf e f cps constrs env hints
    Just (DataPos s)            -> s
    Nothing                     -> Unknown
sizeOf (TEApp _ (TEFold _ _) [tag@(TETag _ _ _)]) f cps constrs env hints = sizeOf tag f cps constrs env hints
sizeOf (TEApp _ (TEUnfold _ _) [arg]) f cps constrs env hints = sizeOf arg f cps constrs env hints
sizeOf (TEApp _ f args) cp cps constrs env hints =
  case controlPointFromExpr f cps of
    Just target ->
      let targetData = controlPointData target
          argEnv = map (\arg -> DataPos $ sizeOf arg cp cps constrs env hints) args
      in sizeOf f cp cps constrs (zip (map fst targetData) argEnv ++ env) hints
    Nothing ->
      case constructorFromExpr f constrs of
        Just constructor ->
          let argTypes = zip args (constructorParameters constructor)
              (nonRecArg, recArgs) = partition (\(e,t) -> t == NonRecursive) argTypes
          in case recArgs of
               []         -> Min
               [(arg, _)] -> C (sizeOf arg cp cps constrs env hints)
               args       -> Multiple $ map (\arg -> C (sizeOf arg cp cps constrs env hints)) (map fst recArgs)
        Nothing -> error "Called function does not exist. This should have been checked by the type checker."
sizeOf (TELet _ id _ p expr body) f cps constrs env hints =
  let params = paramsAsData p
      localDef = Local id f params
      exprSize = sizeOf expr localDef (localDef : cps) constrs (params ++ env) hints
  in sizeOf body f cps constrs ((id, DataPos exprSize) : env) hints
sizeOf (TECase _ expr cases) f cps constrs env hints =
  let exprSize = sizeOf expr f cps constrs env hints
      exprType = getTypeAnno expr
      variant = case exprType of
                     TVari ts          -> ts
                     TRecInd _ (TVari ts) -> ts
                     _                 -> error "Matched expression does not have variant type" -- TODO
      caseTypes id = case lookup id variant of
                          Just tys -> tys
                          Nothing  -> error "Incompatible pattern"
      annoVars (id, (vars, _)) = zip vars (caseTypes id)
      isRecType = (== exprType)
      argEnv c = map (\(v, t) -> if isRecType t then (v, DataPos $ D exprSize) else (v, DataPos $ Var v)) (annoVars c)
      constructor = fst
      caseExpr = snd . snd
      baseCaseSize c = (sizeOf (caseExpr c) f cps constrs ((argEnv c) ++ env) hints) `withAlias` (Min, exprSize)
      recCaseSize c = sizeOf (caseExpr c) f cps constrs ((argEnv c) ++ env) hints
      isBaseCase c = all (\(v,t) -> not $ isRecType t) (annoVars c)
      (baseCases, recCases) = partition isBaseCase cases
      baseCaseSizes = map baseCaseSize baseCases
      recCaseSizes = map recCaseSize recCases
      caseSizes = baseCaseSizes ++ recCaseSizes
      maxSize = if null caseSizes then Unknown else foldr1 max caseSizes -- Gør det mest konservative.
  in case lookup expr hints of
       Just hint ->
         case find (\c -> constructor c == hint) cases of
           Just c -> if isBaseCase c then baseCaseSize c else recCaseSize c
           Nothing -> maxSize
       Nothing -> maxSize
sizeOf (TETag tagty id args) f cps constrs env hints =
  let hasTaggedType arg = case getTypeAnno arg of
                            vari@(TVari _) -> vari == tagty
                            TRecInd _ vari    -> vari == tagty
                            _              -> False
      sizeChangingArgs = filter hasTaggedType args
  in case sizeChangingArgs of
       []    -> Min
       [arg] -> C (sizeOf arg f cps constrs env hints)
       args  -> Multiple $ map (\arg -> C (sizeOf arg f cps constrs env hints)) args
sizeOf _ _ _ _ _ _ = Unknown

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
    in "Terminating functions:\n" ++ (intercalate "\n" $ map showF scgs)

data NonTermination =
    UnsafeMultipathError (Multipath DataEnv (Sym, Size))
  | InfiniteRecursion (Multipath DataEnv (Sym, Size))
  | UnknownCause String

instance Show NonTermination where
  show (UnsafeMultipathError mp) = "Could not determine termination due to unsafe multipath: "
                                   ++ showMultipath mp False
  show (InfiniteRecursion mp)    = "Program is not size-change terminating due to possible infinite recursion in call chain: "
                                   ++ showMultipath mp True
  show (UnknownCause msg)        = show msg

instance Error NonTermination

-- Theorem 4!
isSizeChangeTerminating :: Program -> Either NonTermination Termination
isSizeChangeTerminating []   = return $ Termination []
isSizeChangeTerminating prog =
  let (dataExprs, funExprs) = splitProgram prog
      globalFuns = globalControlPoints funExprs
      globalConstrs = globalDataConstructors dataExprs
      calls = concat $ map (\(cp, e) -> callGraph cp e (map fst globalFuns) globalConstrs (controlPointData cp) []) globalFuns
      sizeChangeGraphs = map sizeChangeGraph calls
      multipaths = concat $ map allMultipaths (cyclicMultipaths sizeChangeGraphs)
      collapsedMultipaths = map (\mp -> (mp, collapse mp)) multipaths
      unsafeMultipaths = map fst $ filter (\(mp, collapsed) -> isNothing collapsed) collapsedMultipaths
      safeCollapsedMultipaths = zip (map fst collapsedMultipaths) (catMaybes $ map snd collapsedMultipaths)
      possiblyNonTerminating =
        filter (\(mp, collapsed) -> isLoop collapsed && isSelfComposition collapsed) safeCollapsedMultipaths
      descendingArcsWithGraph m = map (\(mp, collapsed) -> (mp, descendingArcs (identityArcs collapsed))) m
      graphsWithNoDescendingArcs m = filter (\(mp, arcs) -> null arcs) (descendingArcsWithGraph m)
  in case unsafeMultipaths of
       [] -> case graphsWithNoDescendingArcs possiblyNonTerminating of
         []            -> return $ Termination (map snd safeCollapsedMultipaths)
         nonDescending -> throwError $ UnknownCause (show calls) -- (intercalate ", " $ map (\s -> showSizeChangeGraph s True) sizeChangeGraphs) -- InfiniteRecursion (head $ map fst nonDescending)          
       unsafe -> throwError $ UnsafeMultipathError (head unsafe)
