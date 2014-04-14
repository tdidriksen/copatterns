module Main(main) where

import Test.HUnit

import Expr
import TypeChecker
import TerminationChecker
import TestPrograms


tests :: Test
tests = TestList [TestLabel "subtractSlowly" subtractSlowlyTest]

main :: IO ()
main = do _ <- runTestTT $ tests
          return ()


-- Assertions

assertTermination :: Program -> Assertion
assertTermination p =
  case isSizeChangeTerminating p of
    Right success -> do putStrLn $ show success
                        return ()
    Left failure  -> assertFailure $ show failure

assertNonTermination :: Program -> Assertion
assertNonTermination p =
  case isSizeChangeTerminating p of
    Left success  -> do putStrLn $ show success
                        return ()
    Right failure -> assertFailure $ show failure


-- General test functions

positiveTest :: [Expr] -> Test
positiveTest p =
  TestCase $ (case checkRoot (ERoot p) of
                Right typeCheckedProgram -> assertTermination typeCheckedProgram
                Left e                   -> assertFailure $ show e)


-- Positive tests

subtractSlowlyTest :: Test
subtractSlowlyTest = positiveTest [nat, subtractSlowly]
