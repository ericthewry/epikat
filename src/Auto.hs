module Auto where

import Data.List

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
          deriving (Eq, Ord)

instance Show Cond where
  show (CTest t) = "[" ++ show t ++ "]"
  show (CProg a) = a

-- invariant :: start is minimum integer and final is maxium integer
data Auto =  Auto { start :: Integer
                  , delta :: Map Integer [(Cond, Integer)]
                  , final :: Set Integer
                  } deriving (Eq)

instance Show Auto where
  show auto =
    let stringOf k = if k == (start auto) then ">" else "" ++
                     if Set.member k (final auto) then "(" ++ show k ++ ")" else show k in
    let edge src (cond, tgt) rst =
          stringOf src ++ " --" ++ show cond ++ "--> " ++ stringOf tgt ++ "\n" ++ rst in
    Map.foldrWithKey (\src edges str ->
                         foldr (edge src) "" edges
                         ++ str
                     ) "" (delta auto)

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
                        , final = Set.map (+i) (final auto) }

-- [rename src dst a] replaces every occurence of [src] with [dst] in the automaton
rename :: Integer -> Integer -> Auto -> Auto
rename src dst auto =
  let replace x = if x == src then dst else x in
  Auto { start = replace (start auto)
       , delta = Map.foldrWithKey
                 (\node outArcs rst ->
                     let outArcs' = map (\(c, i) -> (c, replace i)) outArcs in
                     let k' = replace node in
                       Map.insert k' outArcs' rst
                 ) Map.empty (delta auto)
       , final = Set.map replace (final auto)
       }
  

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

-- computes the union of two automata
unionAuto :: Auto -> Auto -> Auto
unionAuto p q =
  let p' = increment 1 $ p in
  let pmax = Set.findMax $ final p' in
  let q' = increment (pmax + 1) $ q in
  let qmax = Set.findMax $ final q' in
  let entermap = Map.singleton 0 [(epsilon, start p'), (epsilon, start q')] in
  let unionFinal = 1 + (if pmax > qmax then pmax else qmax) in
  let exitmap = Set.foldr (extend (epsilon, unionFinal))
                Map.empty
                (final p' `Set.union` final q') in

  Auto { start = 0
       , delta = delta p'
                 `ext_union` delta q'
                 `ext_union` entermap
                 `ext_union` exitmap
       , final = Set.singleton (unionFinal)}


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


completeOne :: Set AtomicTest -> Integer -> [(Cond, Integer)] -> [(Cond, Integer)]
completeOne alphabet dummy edges =
  let (usedAlphabet, allTests) =
        foldr (\ (c, _) (seenAlpha, seenTest) ->
                  case c of
                    CTest t -> (seenAlpha, t `TAnd` seenTest)
                    CProg a -> ((CProg a, dummy) : seenAlpha, seenTest)
              ) ([], TTrue) edges in
  (CTest (TNeg allTests), dummy) : nub usedAlphabet ++ edges
    

completeDelta :: Set AtomicTest -> Integer -> Integer -> [(Cond, Integer)] -> Map Integer [(Cond, Integer)] -> Map Integer [(Cond, Integer) ]
completeDelta alphabet dummy nodeId edges deltaRec =
  let sndEq (_, dstNodeId) (_, dstNodeId') = dstNodeId == dstNodeId' in
  let coterminalEdges = groupBy sndEq edges in
  let extended = map (completeOne alphabet dummy) coterminalEdges in
  Map.insert nodeId (concat extended) deltaRec

-- converts an automaton into a total automaton, i.e. every letter in
-- the alphabet
completeAuto :: Set AtomicTest -> Auto -> Auto
completeAuto alphabet a =
  let dummyState = 1 in
  let a' = rename 1 (start a) (increment 1 a) in
  Auto { start = start a
       , delta = Map.foldrWithKey (completeDelta alphabet dummyState) Map.empty (delta a')
       , final = final a' }
  
        

-- computes the complement of an auto
complementAuto :: Set AtomicTest ->  Auto -> Auto
complementAuto alphabet a =
  let a' = completeAuto alphabet a in
  let states = Set.fromList $
               Map.keys (delta a') ++
               foldr (\ts els ->  (map snd ts) ++ els) [] (Map.elems $ delta a') in

  let final' = states `Set.difference` final a in
  let final'' = if Set.size final' == 0
                then Set.singleton (Set.findMax (final a') + 1)
                else final' in
    Auto { start = start a
         , delta = delta a
         , final = final'' }


-- builds an automaton from an input `Kat` expression
construct :: Kat -> Auto
construct End = Auto { start = 0
                     , delta= Map.empty
                     , final = Set.singleton 1}
                
construct Nop = Auto {start = 0,
                       delta = Map.singleton 0 [(epsilon, 1)],
                       final = Set.singleton 1 }
                
construct (KTest t) = Auto { start = 0
                           , delta = Map.singleton 0 [(CTest t, 1)]
                           , final = Set.singleton 1}

construct (KVar s) = Auto { start = 0
                          , delta = Map.singleton 0 [(CProg s, 1)]
                          , final = Set.singleton 1}
                      
construct (KSeq p q) = construct p `concatAuto` construct q
    
construct (KUnion p q) = construct p `unionAuto` construct q
    
construct (KStar p) = iterateAuto $ construct p
  

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
        let unseenWkList = filter (\(_,nexthop) -> not (Left nexthop `Set.member` Set.fromList p)) worklist in
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
