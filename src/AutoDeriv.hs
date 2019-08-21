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
import GuardedStrings hiding (atomToWorld)

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
    Map.foldrWithKey (\src edges str ->
                         foldr (edge src) "" edges
                         ++ str
                     ) "" (delta auto)


addTrans :: (Ord a, Ord k) => State a k -> Cond -> State a k -> Delta (State a k) Cond -> Delta (State a k) Cond
addTrans s c s' = Map.insertWith (Set.union) s (Set.singleton (c, s'))


setSeq ps qs = Set.fold (\q rst -> Set.map (\p -> KSeq p q) ps `Set.union` rst) Set.empty qs


binop :: (a -> b) -> (b -> b -> b) -> a -> a -> b
binop f op x y = f x `op` f y

atomToWorld :: Atom -> World
atomToWorld = World . posa

nullable :: Atom -> Kat -> Bool
nullable atom KZero = False
nullable atom KEpsilon = False
nullable atom (KVar _) = False
nullable atom (KTest t) = eval (atomToWorld atom) t
nullable atom (KUnion k k') = binop (nullable atom) (||) k k'
nullable atom (KSeq k k') = binop (nullable atom) (&&) k k'
nullable atom (KStar k) = True


deriv :: AtomicProgram -> (Atom, Kat) -> Set Kat
deriv act (atom, KZero) = Set.empty
deriv act (atom, KEpsilon) = Set.empty
deriv act (atom, KVar act') | act == act' = Set.singleton KEpsilon
                           | otherwise = Set.empty
deriv act (atom, KTest _ ) = Set.empty                           
deriv act (atom, KUnion k k') = deriv act (atom, k) `Set.union` deriv act (atom, k')
deriv act (atom, KSeq k k') =
  (if nullable atom k
   then deriv act (atom, k')
   else Set.empty)
  `Set.union`
  Set.fromList [k'' `KSeq` k' | k'' <- Set.toList $ deriv act (atom, k)]

deriv act (atom, k'@(KStar k)) =
  Set.fromList [k'' `KSeq` k' | k'' <- Set.toList $ deriv act (atom, k) ]

derivE :: Atom -> Kat -> Set (State Atom Kat)
derivE atom k = Set.singleton $ AtExp (atom , k)

mkAuto :: [Atom] -> [AtomicProgram] -> Kat -> Auto (State Atom Kat)
mkAuto atoms programs k =
  Auto { start = Exp k
       , delta = transitions atoms programs [Exp k] Map.empty
       , final = Set.singleton (Exp KEpsilon) }

mkAutoL :: [Atom] -> [AtomicProgram] -> Kat -> Auto [State Atom Kat]
mkAutoL atoms programs k =
  let auto = mkAuto atoms programs k in
    Auto { start = [start auto]
         , delta = Map.foldrWithKey
                   (\k edges -> Map.insert [k] (Set.map (\(c, k') -> (c, [k'])) edges))
                   Map.empty (delta auto)
         , final = Set.map (\x -> [x]) (final auto) }


nextHopsA :: Kat -> [Atom] -> [(Cond, State Atom Kat)]
nextHopsA k  = concatMap (\atom ->
                             Set.foldr (\st -> (:) (CAtom atom, st)) [] $
                             derivE atom k)


nextHopsP :: Kat -> Atom -> [AtomicProgram] -> [(Cond, State Atom Kat)]
nextHopsP k atom = concatMap (\act ->
                                 Set.foldr (\k -> (:) (CProg act, Exp k)) []
                                 $ deriv act (atom,k))

                 

-- transitions k worklist agg produces the transition function for an automaton
transitions :: [Atom] -> [AtomicProgram] -> [State Atom Kat] -> Delta (State Atom Kat) Cond  -> Delta (State Atom Kat) Cond
transitions _ _ [] m = m
transitions atoms progs (st@(Exp k) : worklist) m = -- \Delta_a : Expr -> Set (AtExp)
  addAllEdges atoms progs worklist m st $ 
  nextHopsA k atoms
transitions atoms progs (st@(AtExp (atom,k)) : worklist) m =
  addAllEdges atoms progs worklist m st $
  nextHopsP k atom progs

    

addAllEdges atoms progs worklist m st hops =
  let m' = foldr (\(act, st') -> addTrans st act st') m hops in
  if m == m'
  then m'
  else transitions atoms progs (worklist ++ map snd hops) m'  


mkPair :: a -> b -> (a,b)
mkPair a b = (a,b)

-- crossSetWith :: (Ord a, Ord a', Ord b, Ord c) =>
--                 (a -> a' -> c) -> Set (b, a) -> Set (b, a') -> Set (b, c)
crossSetWith combine xs ys =
  Set.foldr
  (\(cx, x) zs -> Set.foldr
  (\(cy, y) zs' ->
      if cx == cy
      then Set.insert (cx,  x `combine` y) zs'
      else zs
  ) zs ys
  ) Set.empty xs

-- crossSet :: (Ord a, Ord a', Ord b) => Set (b, a) -> Set (b, a') -> Set (b, (a,a'))
-- crossSet = crossSetWith mkPair

crossMapWith :: (Ord b, Ord c) =>
                (a -> a' -> b) -> Delta a c -> Delta a' c -> Delta b c
crossMapWith combine m m' =
  Map.foldrWithKey
  (\ k  d xmap -> Map.foldrWithKey
  (\ k' d' ->
     Map.insert (k `combine` k') (crossSetWith combine d d')
  ) xmap m'
  ) Map.empty m

crossMap :: (Ord a, Ord a', Ord b) => Delta a b -> Delta a' b -> Delta (a,a') b
crossMap = crossMapWith mkPair

-- intersectAutoWith :: (Ord a, Ord b, Ord c) => (a -> b -> c) -> Auto a -> Auto b -> Auto c
-- intersectAutoWith combine auto auto' =
--   Auto { start = start auto `combine` start auto'
--        , delta = crossMapWith combine (delta auto) (delta auto')
--        , final = Set.map (\(x, y) -> combine x y) $
--                  final auto `Set.cartesianProduct` final auto'
--        }

intersectAutoL :: (Ord a) => Auto [a] -> Auto [a] -> Auto [a]
intersectAutoL auto auto' =
    Auto { start = start auto ++ start auto'
       , delta = crossMapWith (++) (delta auto) (delta auto')
       , final = Set.map (\(x, y) -> x ++ y) $
                 final auto `Set.cartesianProduct` final auto'
       }
