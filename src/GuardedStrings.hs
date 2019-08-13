module GuardedStrings where

import Prelude hiding (last)

import Data.Set (Set)
import qualified Data.Set as Set

import Syntax
import BDD

-- An atom can be `Empty`, or a sequence of AtomicTests tagged with `Pos` or
-- `Neg`. Intuitively, `AtomicTest`s tagged with `Pos` are true, and
-- `AtomicTest`s tagged with `Neg` are false.
data Atom =
  Empty
  | Pos AtomicTest Atom
  | Neg AtomicTest Atom
  deriving (Eq,Ord)

instance Show Atom where
  show Empty = ""
  show (Pos v Empty) = v
  show (Neg v Empty) = "~" ++ v
  show (Pos v a) = " " ++ v ++ " " ++ show a
  show (Neg v a) = "~" ++ v ++ " " ++ show a
  
-- A guarded String is either a single atom `alpha`, or it is
-- Cons-cell `alpha rho gs`, where `alpha` is an atom, `rho` is a
-- program, and `gs` is a further guarded string.
data GuardedString =
  Single Atom
  | Prog Atom AtomicProgram GuardedString
  deriving (Eq,Ord)

instance Show GuardedString where
  show (Single atom) = "(" ++ show atom ++ ")"
  show (Prog atom prog gs) = "(" ++ show atom ++ ")." ++ prog ++ "." ++ show gs

-- get the first atom of a guarded string
first :: GuardedString -> Atom
first (Single a) = a
first (Prog a _ _ ) = a

-- get the last atom of a guarded strin
last :: GuardedString -> Atom
last (Single a) = a
last (Prog _ _ gs) = last gs

-- `fuse` combines two guarded strings `gs` and `gs'` if `last gs == first gs'`.
-- Otherwise it evaluates to `None`. written in math via `<>`
fuse :: GuardedString -> GuardedString -> Maybe GuardedString
fuse (Single a) (Single b) | a == b = Just $ Single a
                           | otherwise = Nothing
fuse gs (Prog b q gs') = attach gs b q gs'

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
lub gp prev =
  let next = setFuse gp prev `Set.union` prev in
  if next == prev
  then next
  else lub gp next


-- For a given set of atomic tests, i.e. an alphabet, compute all atoms that
-- could arise out of combining the elements of the alphabet
all_atoms :: Set AtomicTest -> [Atom]
all_atoms alphabet =
  Set.foldr (\ letter atoms ->
                map (\x -> Pos letter x) atoms
                ++ map (\x -> Neg letter x) atoms
               ) [Empty] alphabet

-- Convert an atom to corresponding world `Pos` tests are true in the
-- corresponding world, and `Neg` tests are false in the corresponding world.
atomToWorld :: Atom -> Set AtomicTest
atomToWorld Empty = Set.empty
atomToWorld (Pos v a) = Set.insert v $ atomToWorld a
atomToWorld (Neg v a) = atomToWorld a

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
gs_interp :: Set AtomicTest -> Kat -> Set GuardedString
gs_interp alphabet End = Set.empty
gs_interp alphabet Nop =
  let atoms = all_atoms alphabet in
    Set.fromList [Prog a "" (Single a) | a <- atoms]

gs_interp alphabet (KTest t) =
  Set.fromList [(Single a) | a <- induced_atoms alphabet t]
    
gs_interp alphabet (KVar v) =
  let atoms = all_atoms alphabet in
  Set.fromList [ Prog a v (Single b)  | a <- atoms, b <- atoms ]

gs_interp alphabet (KSeq p q) = gs_interp alphabet p `setFuse` gs_interp alphabet q
gs_interp alphabet (KUnion p q) = gs_interp alphabet p `Set.union` gs_interp alphabet q
gs_interp alphabet (KStar p) = lub (gs_interp alphabet p) Set.empty


gs_assertion_interp :: Set AtomicTest -> Test -> Kat -> Set GuardedString
gs_assertion_interp _ _ End = Set.empty
gs_assertion_interp alphabet assertion Nop =
  Set.fromList [Prog a "NOP" (Single a) | a <- induced_atoms alphabet assertion ]

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
