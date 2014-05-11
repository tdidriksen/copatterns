module Main(main) where

import Test.HUnit
import TypeChecker
import Expr
import TestPrograms

-- Util

type CheckEnv = (Env, Env)

envTestLabel, typeTestLabel :: String
envTestLabel = "EnvTest: "
typeTestLabel = "TypeTest: "

tests :: Test
tests = TestList [
                  TestLabel (envTestLabel ++ "dataIsInEnv") dataIsInEnv,
                  TestLabel (typeTestLabel ++ "codataIsInEnv") codataIsInEnv,
                  TestLabel (envTestLabel ++ "letIsInEnv") letIsInEnv,
                  TestLabel (typeTestLabel ++ "simpleUnit") simpleUnit,
                  TestLabel (typeTestLabel ++ "simpleNat") simpleNat,
                  TestLabel (typeTestLabel ++ "simpleVar") simpleVar,
                  TestLabel (typeTestLabel ++ "varFromData") varFromData,
                  TestLabel (typeTestLabel ++ "negativeVar") negativeVar,
                  TestLabel (typeTestLabel ++ "simpleTag") simpleTag,
                  TestLabel (typeTestLabel ++ "negativeTagWrongLabel") negativeTagWrongLabel,
                  TestLabel (typeTestLabel ++ "negativeTagWrongType") negativeTagWrongType,
                  TestLabel (typeTestLabel ++ "simpleFold") simpleFold,
                  TestLabel (typeTestLabel ++ "negativeFold") negativeFold,
                  TestLabel (typeTestLabel ++ "simpleUnfold") simpleUnfold,
                  TestLabel (typeTestLabel ++ "negativeUnfold") negativeUnfold,
                  TestLabel (typeTestLabel ++ "simpleData") simpleData,
                  TestLabel (typeTestLabel ++ "negativeDataWrongName") negativeDataWrongName,
                  TestLabel (typeTestLabel ++ "negativeDataNotRec") negativeDataNotRec,
                  TestLabel (typeTestLabel ++ "simpleCodata") simpleCodata,
                  TestLabel (typeTestLabel ++ "negativeCodataWrongName") negativeCodataWrongName,
                  TestLabel (typeTestLabel ++ "negativeCodataNotRec") negativeCodataNotRec,
                  TestLabel (typeTestLabel ++ "typeSubtractSlowly") typeSubtractSlowly,
                  TestLabel (typeTestLabel ++ "typeSubtractSlowlyWithPred") typeSubtractSlowlyWithPred,
                  TestLabel (typeTestLabel ++ "typeForever") typeForever
                  ]

main :: IO ()
main = do _ <- runTestTT $ tests
          return ()

-- Test

testCheck :: Expr -> CheckEnv -> Either TypeError Type -> Test
testCheck e envs (Left err) = TestCase $ negativeTest e envs err
testCheck e envs (Right t)  = TestCase $ positiveTest e envs t
  
positiveTest :: Expr -> CheckEnv -> Type -> Assertion
positiveTest e (eEnv, tEnv) t = 
  case check eEnv tEnv e of
    Right te -> assertEqual "Resulting type equality" (getTypeAnno te) t
    Left err -> assertFailure $ show err

negativeTest :: Expr -> CheckEnv -> TypeError -> Assertion
negativeTest e (eEnv, tEnv) err =
  case check eEnv tEnv e of
    Right te  -> assertFailure ("Expected error: " ++ (show err) ++ ", but type checking was successful and resulted in " ++ (show te))
    Left aerr -> assertEqual "Resulting error equality" err aerr

inEmpty :: CheckEnv
inEmpty = ([], [])

inRoot :: [Expr] -> CheckEnv
inRoot es =
  case buildRootEnv es of
    Right envs -> envs
    Left err -> error $ show err

inVarEnv :: Env -> CheckEnv
inVarEnv e = (e, [])

toHaveType :: Type -> Either TypeError Type
toHaveType t = return t

toFailWith :: TypeError -> Either TypeError Type
toFailWith e = Left e

testTypeIsInEnv :: (Env, Env) -> Sym -> Type -> Test
testTypeIsInEnv envs s t =
  case lookup s (snd envs) of
    Just t' -> TestCase $ assertEqual "Type in env " t t'
    Nothing -> TestCase $ assertFailure ("Expected " ++ (show s) ++ " to be in environment " ++ (show (snd envs)))

testExprIsInEnv :: (Env, Env) -> Sym -> Type -> Test
testExprIsInEnv envs s t =
  case lookup s (fst envs) of
    Just t' -> TestCase $ assertEqual "Expr in env " t t'
    Nothing -> TestCase $ assertFailure ("Expected " ++ (show s) ++ " to be in environment " ++ (show (fst envs)))

-- Environment Tests

dataIsInEnv :: Test
dataIsInEnv = case buildRootEnv [nat] of
                Right envs -> testTypeIsInEnv envs "nat" natRec
                Left  err  -> TestCase $ assertFailure $ show err

codataIsInEnv :: Test
codataIsInEnv = case buildRootEnv [natStream] of
                  Right envs -> testTypeIsInEnv envs "natStream" natStreamRec
                  Left  err  -> TestCase $ assertFailure $ show err

letIsInEnv :: Test
letIsInEnv = case buildRootEnv [subtractSlowly] of
               Right envs -> testExprIsInEnv envs "subtractSlowly" (TArr [TGlobTypeVar "nat"] (TGlobTypeVar "nat"))
               Left  err  -> TestCase $ assertFailure $ show err

-- Auxiliary Functions Tests

-- Type Tests

--testCheck :: Expr -> CheckEnv -> Either TypeError Type -> Test

simpleUnit :: Test
simpleUnit = testCheck EUnit 
             inEmpty 
            (toHaveType TUnit)

simpleNat :: Test
simpleNat = testCheck nat 
            inEmpty 
           (toHaveType natRec)

simpleVar :: Test 
simpleVar = testCheck (EVar "Z") 
           (inVarEnv [("Z", natRec)]) 
           (toHaveType natRec)

negativeVar :: Test
negativeVar = testCheck (EVar "Z")
              inEmpty
             (toFailWith $ NotInScope "Z")

varFromData :: Test
varFromData = testCheck (EVar "Z") 
             (inRoot [nat])
             (toHaveType natRec)

simpleTag :: Test
simpleTag = testCheck (ETag "Z" [] natBody) 
            inEmpty
           (toHaveType natBody)

negativeTagWrongLabel :: Test
negativeTagWrongLabel = testCheck (ETag "K" [] natBody)
                        inEmpty
                       (toFailWith $ LabelNotFound "K" natBody)

negativeTagWrongType :: Test
negativeTagWrongType = testCheck (ETag "Z" [nat] natBody)
                       inEmpty
                      (toFailWith $ Err "")

simpleFold :: Test
simpleFold = testCheck (EFold natRec) 
             inEmpty
            (toHaveType $ TArr [natBody] natRec)

negativeFold :: Test
negativeFold = testCheck (EFold TUnit)
               inEmpty
              (toFailWith $ Unexpected TUnit "")


simpleUnfold :: Test
simpleUnfold = testCheck (EUnfold natRec)
               inEmpty
              (toHaveType (TArr [natRec] (TRecInd "nat" (TVari [("Z", []), ("S", [natRec])]))))

negativeUnfold :: Test
negativeUnfold = testCheck (EUnfold TUnit)
                 inEmpty
                (toFailWith $ Unexpected TUnit "")

simpleData :: Test
simpleData = testCheck (EData "nat" natRec) 
             inEmpty
            (toHaveType natRec)

negativeDataWrongName :: Test
negativeDataWrongName = testCheck (EData "bat" natRec)
                        inEmpty
                       (toFailWith $ Err "")

negativeDataNotRec :: Test
negativeDataNotRec = testCheck (EData "nat" natBody)
                     inEmpty
                    (toFailWith $ Unexpected natBody "")

simpleCodata :: Test
simpleCodata = testCheck (ECodata "natStream" natStreamRec)
               inEmpty
              (toHaveType natStreamRec)

negativeCodataWrongName :: Test
negativeCodataWrongName = testCheck (ECodata "bat" natStreamRec)
                          inEmpty
                         (toFailWith $ Err "")

negativeCodataNotRec :: Test
negativeCodataNotRec = testCheck (ECodata "nat" TUnit)
                       inEmpty
                      (toFailWith $ Unexpected TUnit "")

typeSubtractSlowly :: Test
typeSubtractSlowly = testCheck subtractSlowly 
                    (inRoot [nat, subtractSlowly]) 
                    (toHaveType (TArr [natRec] natRec))

typeSubtractSlowlyWithPred :: Test
typeSubtractSlowlyWithPred = testCheck subtractSlowlyWithPred 
                            (inRoot [nat, subtractSlowlyWithPred]) 
                            (toHaveType $ TArr [natRec] natRec)

typeForever :: Test
typeForever = testCheck forever 
             (inRoot [nat, forever]) 
             (toHaveType $ TArr [natRec] natRec)

