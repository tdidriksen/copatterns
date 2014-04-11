module Main(main) where

import Test.HUnit
import Data.Char

four :: Int
four = 4
 
tests, test1, test2, test3 :: Test
test1 = TestCase $ assertEqual "test upCase" "FOO" (map toUpper "foo")
test2 = TestCase $ assertEqual "testing that the result is 4" 4 (4::Int)
test3 = TestCase $ assertEqual "testing that 4 is 4" four 3

tests = TestList [TestLabel "test1" test1, TestLabel "test2" test2, TestLabel "test3" test3]

main :: IO ()
main = do _ <- runTestTT $ tests
          return ()
