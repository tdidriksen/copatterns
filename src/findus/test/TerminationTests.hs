module Main(main) where

import Test.HUnit

import Expr
import TypeChecker
import TerminationChecker
import TestPrograms


tests :: Test
tests = TestList [TestLabel "subtractSlowly" subtractSlowlyTest,
                  TestLabel "foreverTest"    foreverTest,
                  TestLabel "scEx1Test"      scEx1Test,
                  TestLabel "scEx3Test"      scEx3Test,
                  TestLabel "scEx4Test"      scEx4Test]

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
                                               assertTermination typeCheckedProgram
                Left e                   -> assertFailure $ show e)


-- Positive tests

subtractSlowlyTest :: Test
subtractSlowlyTest = positiveTest [nat, subtractSlowly]

scEx1Test :: Test
scEx1Test = positiveTest [nat, natList, scEx1]

scEx3Test :: Test
scEx3Test = positiveTest [nat, scEx3]

scEx4Test :: Test
scEx4Test = positiveTest [nat, scEx4]

-- Negative tests

foreverTest :: Test
foreverTest = negativeTest [nat, forever]
