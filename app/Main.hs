module Main where

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Data.Char
import Data.List

import System.Environment (getArgs)

import Syntax
import GuardedStrings
import Epik
import Lexer
import Parser
import FstGen

data Mode = Kat | GS | Auto | Fst deriving (Eq,Show,Ord)

parseArgs :: [String] -> (String, Mode, Int)
parseArgs [] = error "insufficient arguments!"
parseArgs ("gs":n:f:_) = (f, GS, read n)
parseArgs ("fst":f:_) = (f, Fst, (-1))
parseArgs (n:f:_) = (f, GS, read n) -- If no command given, default to GS model
parseArgs args = error ("Unrecognized arguments " ++ intercalate " " args)

process :: String -> (Declarations -> String) -> IO ()
process file fun = readFile file >>= putStrLn . fun . parse

main :: IO ()
main = do
  args <- getArgs
  let (file, mode, num) = parseArgs args
  case mode of
    Kat  -> error "kat printing is disabled"
    GS   -> process file $ showQueryResults num False
    Auto -> error "No automaton model is available yet"
    Fst  -> process file gen_fst
