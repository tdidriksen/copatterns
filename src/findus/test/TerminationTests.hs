module Main(main) where

import Test.HUnit

import Expr
import TypeChecker
import TerminationChecker
import TestPrograms


tests :: Test
tests = TestList [TestLabel "subtractSlowly" subtractSlowlyTest,
                  TestLabel "subtractSlowlyWithPred" subtractSlowlyWithPredTest,
                  TestLabel "foreverTest"    foreverTest,
                  TestLabel "scEx1Test"      scEx1Test,
                  TestLabel "scEx2Test"      scEx2Test,
                  TestLabel "scEx3Test"      scEx3Test,
                  TestLabel "scEx3negTest"   scEx3negTest,
                  TestLabel "scEx4Test"      scEx4Test,
                  TestLabel "scEx4negTest"   scEx4negTest,
                  TestLabel "scEx5Test"      scEx5Test,
                  TestLabel "scEx6Test"      scEx6Test]

main :: IO ()
main = do _ <- runTestTT $ tests
          return ()


-- Assertions

assertTermination :: Program -> Assertion
assertTermination p =
  case isSizeChangeTerminating p of
    Right success -> putStrLn $ show success
    Left failure  -> assertFailure $ show failure

assertNonTermination :: Program -> Assertion
assertNonTermination p =
  case isSizeChangeTerminating p of
    Left success  -> putStrLn $ show success                     
    Right failure -> assertFailure $ show failure


-- General test functions

positiveTest :: [Expr] -> Test
positiveTest p =
  TestCase $ (case checkRoot (ERoot p) of
                Right typeCheckedProgram -> do -- putStrLn $ show typeCheckedProgram
                                               assertTermination typeCheckedProgram
                Left e                   -> assertFailure $ show e)

negativeTest :: [Expr] -> Test
negativeTest p =
  TestCase $ (case checkRoot (ERoot p) of
                Right typeCheckedProgram -> do -- putStrLn $ show typeCheckedProgram
                                               assertNonTermination typeCheckedProgram
                Left e                   -> assertFailure $ show e)


-- Positive tests

subtractSlowlyTest :: Test
subtractSlowlyTest = positiveTest [nat, subtractSlowly]

subtractSlowlyWithPredTest :: Test
subtractSlowlyWithPredTest = positiveTest [nat, subtractSlowlyWithPred]


scEx1Test :: Test
scEx1Test = positiveTest [nat, natList, scEx1]

scEx2Test :: Test
scEx2Test = positiveTest [nat, natList, scEx2f, scEx2g]

scEx3Test :: Test
scEx3Test = positiveTest [nat, scEx3]

scEx4Test :: Test
scEx4Test = positiveTest [nat, scEx4]

scEx5Test :: Test
scEx5Test = positiveTest [nat, natList, scEx5]

scEx6Test :: Test
scEx6Test = positiveTest [nat, natList, scEx6f, scEx6g]


-- Negative tests

foreverTest :: Test
foreverTest = negativeTest [nat, forever]

scEx3negTest :: Test
scEx3negTest = negativeTest [nat, scEx3neg]

scEx4negTest :: Test
scEx4negTest = negativeTest [nat, scEx4neg]
