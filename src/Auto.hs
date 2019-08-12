module Auto where

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import qualified Data.Either as Either

import Syntax
import BDD
import GuardedStrings

-- A transition can occur when the Test succeeds or when the
-- AtomicProgram is at the tape head
data Cond = CTest Test
          | CProg AtomicProgram
          deriving (Eq, Show, Ord)

-- invariant :: start is minimum integer and final is maxium integer
data Auto =  Auto { start :: Integer
                  , delta :: Map Integer [(Cond, Integer)]
                  , final :: Set Integer
                  } deriving (Eq, Show)

-- a well-formed path alternates between Integers and Conds, starting
-- and ending with an Integers
type Path =  [Either Integer Cond]

-- increments the integers in an automaton by `i`
increment :: Integer -> Auto -> Auto
increment i auto = Auto { start = start auto + i
                        , delta = Map.foldrWithKey
                                  (\k a rst ->
                                     let a' = map (\(c, x) -> (c, x + i)) a in
                                       Map.insert (k + i) a' rst
                                  ) Map.empty (delta auto)
                        , final = Set.singleton (start auto + i) }
                        

-- The always-accepting transition
epsilon :: Cond
epsilon = CTest TTrue

-- extend (c,i) k m, sets m[k] to (c,i) : m[k]
extend :: (Cond,Integer) -> Integer -> Map Integer [(Cond, Integer)] -> Map Integer [(Cond, Integer)]
extend (c, p) =
  Map.alter (\value -> case value of
                         Nothing -> Just [(c,p)]
                         Just v -> Just ((c,p) : v))

-- computes the union of two maps, resolving conflicts by appending one list of values to the other
ext_union :: Map Integer [(Cond, Integer)] -> Map Integer [(Cond, Integer)] -> Map Integer [(Cond, Integer)]
ext_union m m' = Map.foldrWithKey (\ k as rst -> foldr (\a -> extend a k) rst as) m m' 
  

-- concatenates two automata
concatAuto :: Auto -> Auto -> Auto
concatAuto pauto quato =
  let pmax = Set.findMax $ final pauto in
  let qauto' = increment (pmax + 1) quato in
  let connection =
        Set.foldr (extend (epsilon, start qauto')) Map.empty (final pauto)
  in
    Auto {start = start pauto
         , delta = delta pauto `ext_union` delta qauto' `ext_union` connection
         , final = final qauto'}

-- takes the "star" of an automaton
iterateAuto pauto = 
  let final_start = -- epsilon transitions from final pauto to start pauto
        Set.foldr (extend (epsilon, start pauto))
        (delta pauto)
        (final pauto) in
    
  let start_final base = -- epsilon transitions from start pauto to final pauto
        Set.foldr (\x -> extend (epsilon, x) (start pauto))
        base
        (final pauto) in
    
  Auto { start = start pauto
       , delta =  start_final final_start
       , final = final pauto}


-- computes the union of two automata
unionAuto :: Auto -> Auto -> Auto
unionAuto pauto qauto =
  let pauto = increment 1 $ pauto in
  let pmax = Set.findMax $ final pauto in
  let qauto = increment (pmax + 1) $ qauto in
  let qmax = Set.findMax $ final qauto in
  let entermap = Map.singleton 0 [(epsilon, start pauto), (epsilon, start qauto)] in

  let exitmap = Set.foldr (extend (epsilon, qmax + 1))
                Map.empty
                (final pauto `Set.union` final qauto) in

  Auto { start = 0
       , delta = delta pauto
                 `ext_union` delta qauto
                 `ext_union` entermap
                 `ext_union` exitmap
       , final = Set.singleton (qmax + 1)}

-- computes the complement of an auto
complementAuto :: Auto -> Auto
complementAuto a =
  let states = Set.fromList (
        Map.keys (delta a) ++
        foldr (\ts els ->  (map snd ts) ++ els) [] (Map.elems (delta a))) in

  let final' = states `Set.difference` final a in
    Auto { start = start a
         , delta = delta a
         , final = final' }


-- builds an automaton from an input `Kat` expression
construct :: Kat -> Auto
construct End = Auto { start = 0
                     , delta= Map.empty
                     , final = Set.empty}
                
construct Nop = Auto {start = 0,
                       delta = Map.singleton 0 [(epsilon, 1)],
                       final = Set.singleton 1 }
                
construct (KTest t) = Auto { start = 0
                           , delta = Map.singleton 0 [(CTest t, 1)]
                           , final = Set.singleton 1}
                      
construct (KSeq p q) = construct p `concatAuto` construct q
    
construct (KUnion p q) = construct p `unionAuto` construct q
    
construct (KStar p) = iterateAuto $ construct p
  
construct (KVar s) = Auto { start = 0
                          , delta = Map.singleton 0 [(CProg s, 1)]
                          , final = Set.singleton 1}

-- `autoDfs a (start a) []` computes all loop-free paths through a network. 
autoDFS :: Auto -> Integer -> Path -> [Path]
autoDFS a state p = 
  if state `Set.member` final a 
  then
    [p]
  else
    case state `Map.lookup` delta a of
      Nothing -> []
      Just worklist ->
        let unseenWkList = filter (\(_,nexthop) -> Left nexthop `Set.member` Set.fromList p) worklist in
          foldr (\(cond, nexthop) rst -> autoDFS a nexthop (p ++ [Right cond, Left nexthop]) ++ rst) [] unseenWkList

-- `normalize nothing p` Inserts unitary tests between consecutive
-- conditions and combines consecutive tests into single tests
normalize :: Maybe Test -> [Cond] -> [Cond]
normalize Nothing [] = [CTest TTrue]
normalize (Just t) [] = [CTest t]
normalize Nothing (CProg p : rst) =  CTest TTrue : CProg p : normalize Nothing rst
normalize (Just t) (CProg p : rst) = CTest t : CProg p : normalize Nothing rst
normalize (Nothing) (CTest t : rst) = normalize (Just t) rst
normalize (Just t) (CTest t' : rst) = normalize (Just $ TAnd t t') rst

-- `gsFromCondList alphabet trace` computes a GuardedString from a trace
-- PRE: cond must be normalized
gsFromCondList :: Set AtomicTest -> [Cond] -> Set GuardedString
gsFromCondList alphabet [] = Set.empty
gsFromCondList alphabet [CTest t] = gs_interp alphabet (KTest t)
gsFromCondList alphabet (CTest t : CProg p : rst) =
  Set.foldr (\ gstring -> Set.union $ Set.fromList $
              (\a -> Prog a p gstring) `map`
              (induced_atoms alphabet t)
            ) Set.empty $
  gsFromCondList alphabet rst
gsFromCondList _ p = error ("Malformed path: " ++ show p ++ "\nPlease normalize the input path to gsFromCondList")

-- Computes the set of GuardedStrings indicated by an automaton path by `normalize`ing and calling `gsFromCondList`.
gsFromPath :: Set AtomicTest -> Path -> Set GuardedString
gsFromPath alphabet path =
  let condsOnly = Either.rights path in
  let normPath = normalize Nothing condsOnly in
  gsFromCondList alphabet normPath


-- Computes the loop-free GuardedStrings (in terms of automaton
-- states) from an automaton
toLoopFreeStrings :: Set AtomicTest -> Auto -> [GuardedString]
toLoopFreeStrings alphabet a =
                foldr (\p rst -> (Set.toList (gsFromPath alphabet p)) ++ rst) [] $
                autoDFS a (start a) [Left (start a)]
