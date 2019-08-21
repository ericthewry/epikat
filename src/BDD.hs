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

mkBranch v b b' = if b == b' then b else Branch v b b'

data World = World (Set AtomicTest)

instance Show World where
  show (World props) = "[" ++ Set.fold (\a -> (++) (" " ++ show a ++ " ")) "]" props

-- Evaluating a BDD in a given world
exec :: World -> BDD -> Bool
exec _ BTrue = True
exec _ BFalse = False
exec world@(World props) (Branch v tru fls) =
  if v `Set.member` props then
    exec world tru
  else
    exec world fls

    
-- evaluates a Test in the context of a World
eval :: World -> Test -> Bool
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
restrictBDD BFalse v = BFalse
restrictBDD x@(Branch v' tru fls) v =
  if v == v' then
    x
  else if v < v' then
    mkBranch v x BFalse
  else
    mkBranch v' (restrictBDD tru v) (restrictBDD fls v)  

-- restricts a BDD to be true if `v` is false
negRestrictBDD :: BDD -> AtomicTest -> BDD
negRestrictBDD BTrue v = Branch v BFalse BTrue
negRestrictBDD BFalse v = BFalse
negRestrictBDD x@(Branch v' tru fls) v =
  if v == v' then
    x
  else if v < v' then
         mkBranch v x BFalse
       else
         mkBranch v' (negRestrictBDD tru v) (negRestrictBDD fls v)

-- computes the union of two BDDs
orBDDs :: BDD -> BDD -> BDD
orBDDs BTrue _ = BTrue
orBDDs _ BTrue = BTrue
orBDDs BFalse y = y
orBDDs x BFalse = x
orBDDs x@(Branch v tru fls) y@(Branch v' tru' fls') =
  if v == v' then
    mkBranch v (tru `orBDDs` tru') (fls `orBDDs` fls')
  else if v < v' then
    mkBranch v (tru `orBDDs` y) (fls `orBDDs` y)
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
andBDDs b@(Branch v tru fls) b'@(Branch v' tru' fls') =
  if v' > v
  then andBDDs b' b
  else if v == v'
  then mkBranch v (tru `andBDDs` tru') (fls `andBDDs` fls')
  else mkBranch v (tru `andBDDs` b') (fls `andBDDs` b')


-- check if a BDD is valid
validBDD :: BDD -> Bool
validBDD BTrue = True
validBDD BFalse = False
validBDD (Branch _ tru fls) = validBDD tru && validBDD fls


-- check if a boolean expression is valid
valid :: Test -> Bool
valid = validBDD . compileBDD
