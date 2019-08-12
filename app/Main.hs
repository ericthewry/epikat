module Main where

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Syntax
import GuardedStrings
import Auto
import Epik

h = TVar "H"
t = TVar "T"
public_announce = ("public_announce", ifElse h (KTest h) $
                                            ifElse t (KTest t) (KTest TFalse))
bob_alternative = ("Bob", Map.fromList [("public_announce", ["public_announce"])])
alice_alternative = ("Alice" , Map.fromList [("public_announce", ["public_announce"])])


htAlpha = Set.fromList ["H", "T"]
htMutex = (h `TAnd` TNeg t) `TOr` (t `TAnd` TNeg h)


prog = Program (htAlpha)
       [htMutex]
       [public_announce]
       [bob_alternative, alice_alternative]
       [("DoesAnnounce?", QIdent ("public_announce"))]

hd [] = undefined
hd (x:_) = x

getAuto (QAuto q) = q
getAuto _ = undefined

autoqueries = foldr (\(_,x) rst -> case x of
                                  QAuto a -> a : rst
                                  _ -> rst
                        ) [] (runQueries prog)
ctx = compileDecls prog
query =
  let Just a = lookupAction (actionsc ctx) "public_announce" in
    katFromAction a
  
  
main :: IO ()
main =
  (putStrLn $ show $ query) >>
  (putStrLn $ show $ construct query) >>
  (putStrLn $ showQueryResults prog)
