module BDD where

import Data.Set (Set)
import qualified Data.Set as Set

import Syntax

-- A BDD is a True-cell, a False-cell, or a Branching statement that
-- evaluates a given atomic test's truth, and chooses a subsequent BDD
-- to evaluate after
data BDD =
  BTrue
  | BFalse
  | Branch AtomicTest BDD BDD
  deriving (Eq, Ord, Show)

-- Evaluating a BDD in a given world
exec :: Set AtomicTest -> BDD -> Bool
exec world BTrue = True
exec world BFalse = False
exec world (Branch v tru fls) =
  if v `Set.member` world then
    exec world tru
  else
    exec world fls

    
-- evaluates a Test in the context of a World
eval :: Set AtomicTest -> Test -> Bool
eval world prop =
  let bdd = compileBDD prop in
  exec world bdd

-- compiles a test into its BDD representation
compileBDD :: Test -> BDD
compileBDD TTrue = BTrue
compileBDD TFalse = BFalse
compileBDD (TVar v) = Branch v BTrue BFalse
compileBDD (TAnd a b) = compileBDD a `andBDDs` compileBDD b
compileBDD (TOr a b) = compileBDD a `orBDDs` compileBDD b
compileBDD (TNeg a) = negBDD $ compileBDD a


-- restricts a BDD to be true iff `v` is true
restrictBDD :: BDD -> AtomicTest -> BDD
restrictBDD BTrue v = Branch v BTrue BFalse
restrictBDD BFalse v = Branch v BFalse BTrue
restrictBDD x@(Branch v' tru fls) v =
  if v == v' then
    x
  else if v < v' then
    Branch v x BFalse
  else
    Branch v' (restrictBDD tru v) (restrictBDD fls v)  

-- restricts a BDD to be true if and only if `v` is false
negRestrictBDD :: BDD -> AtomicTest -> BDD
negRestrictBDD BTrue v = Branch v BFalse BTrue
negRestrictBDD BFalse v = Branch v BTrue BTrue
negRestrictBDD x@(Branch v' tru fls) v =
  if v == v' then
    x
  else if v < v' then
         Branch v x BFalse
       else
         Branch v' (negRestrictBDD tru v) (negRestrictBDD fls v)

-- computes the union of two BDDs
orBDDs :: BDD -> BDD -> BDD
orBDDs BTrue _ = BTrue
orBDDs _ BTrue = BTrue
orBDDs BFalse y = y
orBDDs x BFalse = x
orBDDs x@(Branch v tru fls) y@(Branch v' tru' fls') =
  if v == v' then
    Branch v (tru `orBDDs` tru') (fls `orBDDs` fls')
  else if v < v' then
    Branch v (tru `orBDDs` y) (fls `orBDDs` y)
  else
    y `orBDDs` x

-- Negates a BDD
negBDD :: BDD -> BDD
negBDD BTrue = BFalse
negBDD BFalse = BTrue
negBDD (Branch v tru fls) = Branch v (negBDD tru) (negBDD fls)

-- Computes the conjunction of two BDDs
andBDDs :: BDD -> BDD -> BDD
andBDDs BTrue y = y
andBDDs x BTrue = x
andBDDs BFalse _ = BFalse
andBDDs _ BFalse = BFalse
andBDDs (Branch v tru fls) y =
  restrictBDD (tru `andBDDs` y) v `orBDDs` negRestrictBDD (fls `andBDDs` y) v
