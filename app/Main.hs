module Main where

import Data.Set (Set)
import qualified Data.Set as Set

import Syntax
import Epik



main :: IO ()
main = putStrLn (show $ Program Set.empty [] [] [])
