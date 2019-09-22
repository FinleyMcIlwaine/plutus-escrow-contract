{-# LANGUAGE OverloadedStrings #-}
module Main(main) where

import qualified EscrowTests
import           Test.Tasty

main :: IO ()
main = defaultMain tests

-- | Number of successful tests for each hedgehog property.
--   The default is 100 but we use a smaller number here in order to speed up
--   the test suite.
--

tests :: TestTree
tests = testGroup "Escrow tests" [
    EscrowTests.tests
    ]
