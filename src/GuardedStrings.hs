module GuardedStrings where

import Prelude hiding (last)

import Data.List hiding (last)

import Data.Universe.Helpers
import Data.Maybe

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

fuseL x y = case fuse x y of
              Nothing -> []
              Just z -> [z]

-- `attach` is an auxiliary function implementing `fuse`
attach :: GuardedString -> Atom -> AtomicProgram -> GuardedString -> Maybe GuardedString
attach (Single a) b q gs' | a == b = Just $ Prog a q gs'
                          | otherwise = Nothing
attach (Prog a p gs) b q gs' =
  do attached <- attach gs b q gs'
     Just $ Prog a p attached

-- computes the `fuse` of two guarded strings and inserts the result into to a set
-- thereof if the `fuse` succeeds, otherwise, just return the set
inner :: GuardedString -> GuardedString -> [GuardedString] -> [GuardedString]
inner x y strings = case fuse x y of
                      Nothing -> strings
                      Just xy -> [xy] ++ strings

-- for a GuardedString `gs` and a set `X`, compute `gs <> X`.
fuseCoset :: GuardedString -> [GuardedString] -> [GuardedString]
fuseCoset x = foldr (inner x) [] 

-- for two sets of guarded strings `X` and `Y`, compute `X <> Y`
listFuse :: [GuardedString] -> [GuardedString] -> [GuardedString]
-- listFuse xs ys =
--   foldr (\x rst -> fuseCoset x ys ++ rst) [] xs
listFuse xs ys = mapMaybe (uncurry fuse) (xs +*+ ys)


permute :: [a] -> [a]
permute = id -- head . take 5 . permutations

-- Compute the fixpoint of the set-lifted fuse operation
lubG :: Integer -> [GuardedString] -> [GuardedString] -> [GuardedString]
lubG 0 _ prev = prev
lubG gas gStrings prev =
  permute prev
  +++
  let next = (gStrings `listFuse` prev) in
    if next == prev then next else lubG (gas-1) gStrings next

lubInf :: [GuardedString] -> [GuardedString] -> [GuardedString]
lubInf gStrings prev =
  permute prev +++
    let next = (gStrings `listFuse` prev) in
      if next == prev then next else lubInf gStrings next
  

takeUnique :: Int -> [GuardedString] -> [GuardedString]
takeUnique = takeUniqueAux []
  where takeUniqueAux seen i [] = []
        takeUniqueAux seen 0 _ = []
        takeUniqueAux seen i (x:xs)
          | x `elem` seen = takeUniqueAux seen i xs
          | otherwise     = x : takeUniqueAux (x:seen) (i-1) xs


fixpointGS :: [Atom] -> [GuardedString] -> [GuardedString]
fixpointGS atoms gs = lubG 10 gs $ map Single atoms


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

-- For a given set of atomic tests, i.e. an alphabet, compute all atoms that
-- could arise out of combining the elements of the alphabet
allAtoms :: Set AtomicTest -> [Atom]
allAtoms alphabet =
  Set.foldr (\ letter atoms ->
                map (addPos letter) atoms
                ++ map (addNeg letter) atoms
               ) [Atom Set.empty Set.empty] alphabet

-- Computes all atoms in which the test `t` evaluates to True
inducedAtoms :: Test ->  [Atom] -> [Atom]
inducedAtoms t = filter (\ a -> evalAtom a t)

-- Interprets a `Kat` expression in a given alphabet, producing its corresponding set of guarded strings
-- [| p |]^X subset of GuardedString
gs_interp :: [Atom] -> Kat -> [GuardedString]
gs_interp atoms KZero = []
gs_interp atoms KEpsilon =
  [(Single a) | a <- atoms]
 
gs_interp atoms (KTest t) =
  [(Single a) | a <- inducedAtoms t atoms]
    
gs_interp atoms (KVar v) =
  [ Prog a v (Single b)  | a <- atoms, b <- atoms ]

gs_interp atoms (KSeq p q) = gs_interp atoms p `listFuse` gs_interp atoms q
gs_interp atoms (KUnion p q) = gs_interp atoms p +++ gs_interp atoms q
gs_interp atoms (KStar p) = fixpointGS atoms $ gs_interp atoms p



gsLen :: GuardedString -> Int
gsLen (Single _) = 0
gsLen (Prog _ _ gs) = 1 + gsLen gs
