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

ht_no_change_program = ifElse h (KTest h) $ ifElse t (KTest t) (KTest TFalse)

htAlpha = Set.fromList ["H", "T"]
htMutex = (h `TAnd` TNeg t) `TOr` (t `TAnd` TNeg h)

-- atomic actions
heads = "H"
tails = "T"
-- agents
alice = "alice"
bob = "bob"

-- helper
test_prop ht = KTest $ TVar ht

-- Programs
public_announce :: AtomicTest -> AtomicProgram
public_announce ht = "public_announce_" ++ ht

noop :: AtomicProgram
noop = "no_operation"

peeksAt, sneaksALookAt :: Agent -> AtomicTest -> AtomicProgram
peeksAt agent ht = agent ++ "_peek_" ++ ht
sneaksALookAt agent ht = agent ++ "_sneak_" ++ ht

-- helper
test_prog name ht = (name ht, test_prop ht)


-- Alternative Relation
alice_alternative = ("Alice" ,
                     Map.fromList [(public_announce heads, [public_announce heads]),
                                   (public_announce tails, [public_announce tails]),
                                   (alice `peeksAt` heads, [alice `peeksAt` heads]),
                                   (alice `peeksAt` tails, [alice `peeksAt` tails]),
                                   (alice `sneaksALookAt` heads, [alice `sneaksALookAt` heads]),
                                   (alice `sneaksALookAt` tails, [alice `sneaksALookAt` heads]),
                                   (bob `peeksAt` heads, [bob `peeksAt` heads, bob `peeksAt` tails]),
                                   (bob `peeksAt` tails, [bob `peeksAt` tails, bob `peeksAt` tails]),
                                   (bob `sneaksALookAt` heads, [noop]),
                                   (bob `sneaksALookAt` tails, [noop])
                                  ])

bob_alternative = ("Bob",
                   Map.fromList [(public_announce heads, [public_announce heads]),
                                 (public_announce tails, [public_announce tails]),
                                 (alice `peeksAt` heads, [alice `peeksAt` tails, alice `peeksAt` heads]),
                                 (alice `peeksAt` tails, [alice `peeksAt` heads, alice `peeksAt` heads]),
                                 (bob `peeksAt` heads, [bob `peeksAt` heads]),
                                 (bob `peeksAt` tails, [bob `peeksAt` tails]),
                                 (alice `sneaksALookAt` heads, [noop]),
                                 (alice `sneaksALookAt` tails, [noop]),
                                 (bob `sneaksALookAt` heads, [bob `sneaksALookAt` heads]),
                                 (bob `sneaksALookAt` tails, [bob `sneaksALookAt` tails])
                                 ])                    




-- A Hypothesis for the knowledge query.
-- [know x t] is a literal translation of K_x(t) from the writeup
knows :: Agent -> Query -> Query
knows x query = QComplement (QIdent x `QApply` (QComplement query))


-- public_announce_H + public_announce_T
public_announce_query =
  foldr1 (QUnion) $
  map (QIdent . public_announce) [heads,tails]

ever query = (QStar QAll) `QConcat` query `QConcat`(QStar QAll)

prog = Program
  (Set.fromList [heads, tails]) -- alphabet
  [htMutex]  -- assertion
  [(noop, Nop),
   test_prog public_announce heads, ----- > H; public_announce_H; H
   test_prog public_announce tails, ----- > T; public_announce_T; T
   test_prog (peeksAt alice) heads, 
   test_prog (peeksAt alice) tails,
   test_prog (peeksAt bob) heads,
   test_prog (peeksAt bob) tails,
   test_prog (sneaksALookAt alice) heads,
   test_prog (sneaksALookAt bob) tails,
   test_prog (sneaksALookAt bob) heads,
   test_prog (sneaksALookAt bob) tails
  ]
  [bob_alternative, alice_alternative]
  [("EverAnnounces?", ever public_announce_query)]
  
hd [] = undefined
hd (x:_) = x

getAuto (QAuto q) = q
getAuto _ = undefined

autoqueries = foldr (\(_,x) rst -> case x of
                                  QAuto a -> a : rst
                                  _ -> rst
                        ) [] (runQueries prog)
-- ctx = compileDecls prog
-- query =
--   let Just a = lookupAction (actionsc ctx) "public_announce" in
--     katFromAction a
  
  
main :: IO ()
main =
  -- (putStrLn $ show $ query) >>
  -- (putStrLn $ show $ construct query) >>
  (putStrLn $ showQueryResults prog)
