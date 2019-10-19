module AutoDeriv where

import Data.List

import Data.Maybe

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
data Cond = CAtom Atom
          | CProg AtomicProgram
          deriving (Eq, Ord)

instance Show Cond where
  show (CAtom t) = show t
  show (CProg a) = show a


data State a k = Exp k
               | AtExp (a, k)
               deriving (Eq, Ord)

instance (Show a, Show k) => Show (State a k) where
  show (Exp k) = "<" ++ show k ++ ">"
  show (AtExp (a, k)) = "<" ++ show a ++ "," ++ show k ++ ">"


type Delta a b = Map a (Set (b, a))

sources :: Delta a b -> [a]
sources = Map.foldrWithKey' (\k succ rst -> if Set.null succ then rst else k:rst) []

states :: Delta a b -> [a]
states d = Map.keys d ++ concatMap (Set.fold ((:) . snd) []) (Map.elems d)

-- invariant :: start is minimum integer and final is maxium integer
data Auto a =  Auto { start :: a
                  , delta :: Delta a Cond
                  , final :: Set a
                  } deriving (Eq)

instance (Ord a, Show a) => Show (Auto a) where
  show auto =
    let stringOf k = (if k == (start auto) then ">" else "") ++
                     if Set.member k (final auto) then "(" ++ show k ++ ")" else show k in
    let edge src (cond, tgt) rst =
          stringOf src ++ " --" ++ show cond ++ "--> " ++ stringOf tgt ++ "\n" ++ rst in
    Map.foldrWithKey' (\src edges str ->
                         foldr (edge src) "" edges
                         ++ str
                     ) "" (delta auto)


addTrans :: (Ord a, Ord k) => State a k -> Cond -> State a k -> Delta (State a k) Cond -> Delta (State a k) Cond
addTrans s c s' = Map.insertWith (Set.union) s (Set.singleton (c, s'))


setSeq ps qs = Set.fold (\q rst -> Set.map (\p -> kseq p q) ps `Set.union` rst) Set.empty qs

binop :: (a -> b) -> (b -> b -> b) -> a -> a -> b
binop f op x y = f x `op` f y


accepting :: State Atom (Kat p) -> Bool
accepting (AtExp (at, expr)) = nullable at expr
accepting (Exp _) = False

nullable :: Atom -> (Kat p) -> Bool
nullable atom KZ = False
nullable atom KEps = True
nullable atom (KNeg k) = not (nullable atom k)
nullable atom (KEvent _) = False
nullable atom (KBool t) = eval (atomToWorld atom) t
nullable atom (KPlus k k') = binop (nullable atom) (||) k k'
nullable atom (KSequence k k') = binop (nullable atom) (&&) k k'
nullable atom (KAnd k k') = binop (nullable atom) (&&) k k'
nullable atom (KIter k) = True
nullable atom (KApply _ k) = nullable atom k -- [TODO] Maybe Correct?

deriv' :: (Ord p, Show p) =>
  p
  -> (Agent -> p -> Maybe [(Atom, p, Atom)])
  -> (Atom, Kat (Atom, p, Atom))
  -> (Atom, Kat (Atom, p, Atom))
deriv' act _ (atom, KZ) = (atom, kzero)
deriv' act _ (atom, KEps) = (atom, kzero)
deriv' act f (atom, KEvent (pre', act', post'))
  | atom == pre'
  = case f "GOD" act of
      Nothing -> error ("No GOD for " ++ show act)
      Just conds -> if (pre', act', post') `elem` conds
                    then (post', kepsilon)
                    else (post', kzero)
  | otherwise = kzero
deriv' act _ (atom, KBool _ ) = (atom, kzero)
deriv' act f (atom, KPlus k k') = -- ASSUMPTION :: ACTIONS ARE DETERMINISTIC
  let (_, dk) =  deriv' act f (atom, k) in
  let (_, dk') = deriv' act f (atom, k) in
  let alts = f "GOD" act in
  case find alts (\(pre, a, post) -> pre == atom && a == act) of
    Nothing -> error ("No God for " ++ show atom ++ show act)
    (Just (_, _, post)) -> (post, dk `kunion` dk')
      
deriv' act f (atom, KAnd k k') =
  deriv' act f (atom, k) `kand` deriv' act f (atom, k')
deriv' act f (atom, KSequence k k') =
  (if nullable atom k
   then deriv' act f (atom, k')
   else kzero)
  `kunion`
  deriv' act f (atom, k) `kseq` k'

deriv' act f (atom, KApply agent k) =
  case f agent act of
    Nothing -> error ("could not find agent " ++ agent ++ " and action " ++ show act)
    Just alts ->
      foldr kunion kzero $
      [ kapply agent $ deriv' alt f (post, k)
      | (pre, alt, post) <- alts
      , pre == atom ]

deriv' act f (atom, ks@(KIter k)) =
  (deriv' act f (atom, k)) `kseq` ks

deriv' act _ (atom, KNeg KZ) = (atom, kzero)
deriv' act _ (atom, KNeg KEps) = (atom, kzero)
deriv' act f (atom, KNeg (KEvent (pre', act', post')))
  | atom == pre'
  =
  if act == act' then (atom, kzero) else
    case f "GOD" act of
      Nothing -> error ("No GOD for " ++ show act)
      Just conds ->
        foldr kunion kzero $
        [ katom (posa post) | (_, _, post) <- conds ]

  | otherwise = kzero
deriv' act f (atom, KNeg k) = kneg $ deriv' act f (atom, k)  



derivE :: Atom -> Kat p -> Set (State Atom (Kat p))
derivE atom k = Set.singleton $ AtExp (atom , k)

mkAuto :: [Atom] -> [AtomicProgram]
       -> (Agent -> AtomicProgram -> Maybe [(Atom, AtomicProgram, Atom)])
       -> Kat (Atom, AtomicProgram, Atom) -> Auto (State Atom (Kat (Atom, AtomicProgram, Atom)))
mkAuto atoms programs f k = 
  let delta = transitions atoms programs f [Exp k] Map.empty in
  Auto { start = Exp k
       , delta = delta
       , final = Set.filter accepting (Set.fromList $ states delta)   }

mkAutoL :: [Atom] -> [AtomicProgram] 
        -> (Agent -> AtomicProgram -> Maybe [(Atom, AtomicProgram, Atom)])
        -> Kat (Atom, AtomicProgram, Atom) -> Auto [State Atom (Kat (Atom, AtomicProgram, Atom))]
mkAutoL atoms programs f k =
  let auto = mkAuto atoms programs f k in
    Auto { start = [start auto]
         , delta = Map.foldrWithKey'
                   (\k edges -> Map.insert [k] (Set.map (\(c, k') -> (c, [k'])) edges))
                   Map.empty (delta auto)
         , final = Set.map (\x -> [x]) (final auto) }


nextHopsA :: (Kat (Atom, AtomicProgram, Atom)) -> [Atom] -> [(Cond, State Atom (Kat (Atom, AtomicProgram, Atom)))]
nextHopsA k  = concatMap (\atom ->
                              Set.foldr' (\st -> (:) (CAtom atom, st)) [] $
                              derivE atom k)


nextHopsP :: Kat (Atom, AtomicProgram, Atom)
          -> Atom
          -> [AtomicProgram]
          -> (Agent -> AtomicProgram -> Maybe [(Atom, AtomicProgram, Atom)])
          -> [(Cond, State Atom (Kat (Atom, AtomicProgram, Atom)))]
nextHopsP k atom progs f =
  map (\act ->
          (CProg act, Exp $ deriv' act f (atom,k)))
  progs

                 

-- transitions k worklist agg produces the transition function for an automaton
transitions :: [Atom]
            -> [AtomicProgram]
            -> (Agent -> AtomicProgram -> Maybe [(Atom, AtomicProgram, Atom)])
            -> [State Atom (Kat (Atom, AtomicProgram, Atom))]
            -> Delta (State Atom (Kat (Atom, AtomicProgram, Atom))) Cond
            -> Delta (State Atom (Kat (Atom, AtomicProgram, Atom))) Cond
transitions _ _ f [] m = m
transitions atoms progs f (st@(Exp k) : worklist) m = -- \Delta_a : Expr -> Set (AtExp)
   addAllEdges atoms progs f worklist m st $ 
   nextHopsA k atoms
transitions atoms progs f (st@(AtExp (atom,k)) : worklist) m =
   addAllEdges atoms progs f worklist m st $
   nextHopsP k atom progs f

    
addAllEdges :: [Atom]
            -> [AtomicProgram]
            -> (Agent -> AtomicProgram -> Maybe [(Atom, AtomicProgram, Atom)])
            -> [State Atom (Kat (Atom, AtomicProgram, Atom))]
            -> Delta (State Atom (Kat (Atom, AtomicProgram, Atom))) Cond
            -> State Atom (Kat (Atom, AtomicProgram, Atom))
            -> [(Cond, State Atom (Kat (Atom, AtomicProgram, Atom)))]
            -> Delta (State Atom (Kat (Atom, AtomicProgram, Atom))) Cond
addAllEdges atoms progs f worklist m st hops =
   let m' = foldr (\(act, st') -> addTrans st act st') m hops in
   if m == m' && foldr (\x acc -> x `elem` sources m && acc ) True worklist 
   then m'
   else transitions atoms progs f (worklist ++ map snd hops) m'  

-- crossSetWith :: (Ord a, Ord a', Ord b, Ord c) =>
--                 (a -> a' -> c) -> Set (b, a) -> Set (b, a') -> Set (b, c)
crossSetWith combine xs ys =
  Set.fromList [(c, combine x y) | (c, x) <- Set.toList xs
                                 , (c', y) <- Set.toList ys
                                 , c == c']

-- crossSet :: (Ord a, Ord a', Ord b) => Set (b, a) -> Set (b, a') -> Set (b, (a,a'))
-- crossSet = crossSetWith mkPair

crossMapWith :: (Ord b, Ord c) =>
                (a -> a' -> b) -> Delta a c -> Delta a' c -> Delta b c
crossMapWith combine m m' =
  Map.foldrWithKey'
  (\ k  d xmap -> Map.foldrWithKey'
  (\ k' d' ->
     Map.insert (k `combine` k') (crossSetWith combine d d')
  ) xmap m'
  ) Map.empty m

crossMap :: (Ord a, Ord a', Ord b) => Delta a b -> Delta a' b -> Delta (a,a') b
crossMap = crossMapWith (,)

intersectAutoL :: (Ord a) => Auto [a] -> Auto [a] -> Auto [a]
intersectAutoL auto auto' =
    Auto { start = start auto ++ start auto'
       , delta = crossMapWith (++) (delta auto) (delta auto')
       , final = Set.map (\(x, y) -> x ++ y) $
                 final auto `Set.cartesianProduct` final auto'
       }

loopFreeStrings :: (Ord a, Eq a) => Auto a -> Set (Maybe GuardedString)
loopFreeStrings auto =
  pathToString `Set.map`
  loopFreePaths [] (start auto) auto


pathToString :: [Cond] -> Maybe GuardedString
pathToString [] = Nothing
pathToString [CAtom a] = Just $ Single a
pathToString (CAtom a:CProg p:cs) = Just . Prog a p =<< pathToString cs
pathToString gs = error $ "Malformed guardedstring " ++ foldr ((++) . show) "" gs


loopFreePaths :: (Eq st, Ord st) => [st] -> st -> Auto st -> Set [Cond]
loopFreePaths path curr auto 
  | curr `Set.member` final auto = Set.singleton []
  | curr `elem` path = Set.empty
  | otherwise =
    case curr `Map.lookup` delta auto of
      Nothing -> Set.empty
      Just succs ->
        Set.foldr' (\(cond,succ) -> Set.union (Set.map ((:) cond) $ loopFreePaths (curr:path) succ auto))
        Set.empty succs  
