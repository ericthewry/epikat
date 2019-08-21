module GuardedStrings where

import Prelude hiding (last)

import Data.Set (Set)
import qualified Data.Set as Set

import Syntax
import BDD

data Atom =
  Atom { posa :: (Set AtomicTest),
         nega :: (Set AtomicTest) }
  deriving (Eq, Ord)

instance Show Atom where
  show (Atom pos neg) =
    let join a rst = (if Set.member a neg then "~" else "") ++ show a ++ "" ++ rst in 
    "(" ++ Set.fold join "" (Set.union pos neg) ++ ")"
    -- Set.fold  "" pos ++
    -- Set.fold (\a -> (++) ("~" ++ show a ++ "")) "" neg ++ ")"

addPos :: AtomicTest -> Atom -> Atom
addPos t a = Atom { posa = Set.insert t (posa a)
                  , nega = Set.delete t (nega a) }

addNeg :: AtomicTest -> Atom -> Atom
addNeg t a = Atom { posa = Set.delete t (posa a)
                  , nega = Set.insert t (nega a) }

testOfAtom :: Atom -> Test
testOfAtom (Atom pos neg) =
  Set.foldr (TAnd . TVar) (Set.foldr (TAnd . TNeg . TVar) TTrue neg) pos
  
-- A guarded String is either a single atom `alpha`, or it is
-- Cons-cell `alpha rho gs`, where `alpha` is an atom, `rho` is a
-- program, and `gs` is a further guarded string.
data GuardedString =
  Single Atom
  | Prog Atom AtomicProgram GuardedString
  deriving (Eq,Ord)

instance Show GuardedString where
  show (Single atom) = "(" ++ show atom ++ ")"
  show (Prog atom prog gs) = "(" ++ show atom ++ ")." ++ show prog ++ "." ++ show gs

-- get the first atom of a guarded string
first :: GuardedString -> Atom
first (Single a) = a
first (Prog a _ _ ) = a

-- get the last atom of a guarded strin
last :: GuardedString -> Atom
last (Single a) = a
last (Prog _ _ gs) = last gs

-- `fuse` combines two guarded strings `gs` and `gs'`
--  if `last gs == first gs'`.
-- Otherwise it evaluates to `None`. written in math via `<>`
fuse :: GuardedString -> GuardedString -> Maybe GuardedString
-- fuse (Single a) (Single b) | a == b = Just $ Single a
--                            | otherwise = Nothing
fuse gs (Prog b q gs') = attach gs b q gs'
fuse gs (Single b) | last gs == b = Just gs
                   | otherwise = Nothing

-- `attach` is an auxiliary function implementing `fuse`
attach :: GuardedString -> Atom -> AtomicProgram -> GuardedString -> Maybe GuardedString
attach (Single a) b q gs' | a == b = Just $ Prog a q gs'
                          | otherwise = Nothing
attach (Prog a p gs) b q gs' =
  do attached <- attach gs b q gs'
     Just $ Prog a p attached

-- computes the `fuse` of two guarded strings and inserts the result into to a set
-- thereof if the `fuse` succeeds, otherwise, just return the set
inner :: GuardedString -> GuardedString -> Set GuardedString -> Set GuardedString
inner x y strings = case fuse x y of
                      Nothing -> strings
                      Just xy -> Set.insert xy strings

-- for a GuardedString `gs` and a set `X`, compute `gs <> X`.
fuseCoset :: GuardedString -> Set GuardedString -> Set GuardedString
fuseCoset x = Set.foldr (inner x) Set.empty 
              
-- for two sets of guarded strings `X` and `Y`, compute `X <> Y`
setFuse :: Set GuardedString -> Set GuardedString -> Set GuardedString
setFuse xs ys =
  Set.foldr (\x strings -> fuseCoset x ys `Set.union` strings) Set.empty xs

-- Compute the fixpoint of the set-lifted fuse operation
lub :: Set GuardedString -> Set GuardedString -> Set GuardedString
lub gsSet prev =
  let next = (gsSet `setFuse` prev) `Set.union` prev in
  if next == prev
  then next
  else lub gsSet next

fixpointGS :: Set GuardedString -> Set GuardedString
fixpointGS gs = lub gs Set.empty

-- For a given set of atomic tests, i.e. an alphabet, compute all atoms that
-- could arise out of combining the elements of the alphabet
all_atoms :: Set AtomicTest -> [Atom]
all_atoms alphabet =
  Set.foldr (\ letter atoms ->
                map (addPos letter) atoms
                ++ map (addNeg letter) atoms
               ) [Atom Set.empty Set.empty] alphabet

-- Convert an atom to corresponding world `Pos` tests are true in the
-- corresponding world, and `Neg` tests are false in the corresponding world.
atomToWorld :: Atom -> World
atomToWorld = World . posa

-- Executes a BDD in the context of an atom 
execAtom :: Atom -> BDD -> Bool
execAtom a b = exec (atomToWorld a) b

-- Executes a Test in the context of an Atom
evalAtom :: Atom -> Test -> Bool
evalAtom a = eval (atomToWorld a)

-- Computes all atoms in which the test `t` evaluates to True
induced_atoms :: Set AtomicTest -> Test -> [Atom]
induced_atoms alphabet t = filter (\ a -> evalAtom a t) $ all_atoms alphabet 

-- Interprets a `Kat` expression in a given alphabet, producing its corresponding set of guarded strings
-- [| p |]^X subset of GuardedString
gs_interp :: Set AtomicTest -> Kat -> Set GuardedString
gs_interp alphabet KZero = Set.empty
gs_interp alphabet KEpsilon =
  let atoms = all_atoms alphabet in
    Set.fromList [Prog a (AtomicProgram "1") (Single a) | a <- atoms]

gs_interp alphabet (KTest t) =
  Set.fromList [(Single a) | a <- induced_atoms alphabet t]
    
gs_interp alphabet (KVar v) =
  let atoms = all_atoms alphabet in
  Set.fromList [ Prog a v (Single b)  | a <- atoms, b <- atoms ]

gs_interp alphabet (KSeq p q) = gs_interp alphabet p `setFuse` gs_interp alphabet q
gs_interp alphabet (KUnion p q) = gs_interp alphabet p `Set.union` gs_interp alphabet q
gs_interp alphabet (KStar p) = fixpointGS (gs_interp alphabet p)


gs_assertion_interp :: Set AtomicTest -> Test -> Kat -> Set GuardedString
gs_assertion_interp _ _ KZero = Set.empty
gs_assertion_interp alphabet assertion KEpsilon =
  Set.fromList [Prog a (AtomicProgram "1") (Single a) | a <- induced_atoms alphabet assertion ]

gs_assertion_interp alphabet assertion (KTest t) =
  Set.fromList [(Single a) | a <- induced_atoms alphabet (assertion `TAnd` t) ]

gs_assertion_interp alphabet assertion (KVar v) =
  let atoms = induced_atoms alphabet assertion in
  Set.fromList [ Prog a v (Single b) | a <- atoms, b <- atoms ]

gs_assertion_interp alphabet assertion (KSeq p q) = gs_assertion_interp alphabet assertion p
                                                     `setFuse` gs_assertion_interp alphabet assertion q
gs_assertion_interp alphabet assertion (KUnion p q) = gs_assertion_interp alphabet assertion p
                                                       `Set.union` gs_assertion_interp alphabet assertion q
gs_assertion_interp alphabet assertion (KStar p) = lub (gs_assertion_interp alphabet assertion p) Set.empty
