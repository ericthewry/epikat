module Epik where

import Prelude hiding (last, negate)

import Data.List hiding (last, intersect)

import Data.Universe.Helpers

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Data.Maybe

import qualified Data.Either as Either

{- INTERNAL MODULES -}
import Syntax
import GuardedStrings
import BDD
import AutoDeriv
{- END INTERNAL MODULES -}
  
data Action = Action { name :: AtomicProgram
                     , program :: Kat
                     } deriving (Eq, Show)

nameStr :: Action -> String
nameStr = show . name

lookupAction :: AtomicProgram -> [Action] -> Maybe Action
lookupAction p = find (\a -> name a == p)

  
data Context =
  Context { alphabetc :: Set AtomicTest
          , atomsc :: [Atom]
          , assertion :: Test
          , actionsc :: [Action]
          , viewsc :: [(Agent, Map AtomicProgram [AtomicProgram])]}


instance Show Context where
  show ctx = "Context { alphabetc = " ++ show (alphabetc ctx)
             ++ ", actionsc = " ++ show (actionsc ctx)
             ++ ", viewsc = [" ++ intercalate ", " (map (\(agent, _) -> agent ++ " : <func>") (viewsc ctx)) ++ "]"




compileAction :: AtomicProgram -> Kat -> Action
compileAction name k =
  Action { name = name, program = subst (AtomicProgram "id") name k }

-- substiutes every occurence of obs for rplc in kat expr
subst obs rplc KZero = KZero
subst obs rplc KEpsilon = KEpsilon
subst obs rplc (KTest t) = (KTest t)
subst obs rplc (KVar x) | obs == x = KVar rplc
                        | otherwise = KVar x
subst obs rplc (KSeq k k') =
  subst obs rplc k `KSeq` subst obs rplc k'
subst obs rplc (KUnion k k') =
  subst obs rplc k `KUnion` subst obs rplc k'
subst obs rplc (KStar k) =
  KStar $ subst obs rplc k


compileDecls :: Declarations -> Context
compileDecls (Program alphabet asserts actions views queries) =
  let assertion = foldr TAnd TTrue asserts in
  let atoms = inducedAtoms assertion $ allAtoms alphabet in
  Context { alphabetc = alphabet
          , atomsc = atoms
          , assertion = assertion
          , actionsc = map (\(n, p) -> compileAction n p) actions
          , viewsc = views
          }

scopeFor :: [(QueryName, Query)] -> QueryName -> [(QueryName, Query)]
scopeFor qs name = takeWhile (\(n, _) -> n /= name) qs

atomicActions :: Context -> Set AtomicProgram
atomicActions ctx = foldr (\x -> Set.insert (name x)) Set.empty (actionsc ctx)

-- atomsCtx :: Context -> [Atom]
-- atomsCtx ctx = inducedAtoms (assertion ctx) $ allAtoms (alphabetc ctx)

runQueries :: Declarations -> [(QueryName, [GuardedString])]
runQueries decls =
  let context = compileDecls decls in
  mapSnd (computeGuardedStrings context) $ queries decls

mapSnd :: (b -> c) -> [(a,b)] -> [(a,c)]
mapSnd _ [] = []
mapSnd f ((x,y):xs) = (x, f y) : mapSnd f xs
  

accShow :: Show a => String -> a -> String -> String
accShow sep x str = sep ++ show x ++ str

showQueryResults :: Int -> Declarations -> String
showQueryResults num decls =
  let queries = runQueries decls in
    foldr (\(name, gsTraces) accStr ->
                let gsStr = foldr (accShow "\n\t") "\n" (sortOn gsLen$ take num gsTraces)  in
                  name ++ " identifies the following (loop-free) strings:\n" ++ gsStr ++  "-----\n\n" ++ accStr
             -- name ++ " produces the automaton: \n " ++ show auto ++ "----\n\n" ++ accStr
          ) "" queries


showKatTerms :: Declarations -> String
showKatTerms decls =
  let ctx = compileDecls decls in
    concatMap (\(n, ks) -> n ++ " becomes KAT expressions: \n" ++
                concatMap (\k -> "\t" ++ show k ++ "\n") ks ++ "\n") $
    mapSnd (desugar ctx) $ queries decls



----------------------------------------------------------------------------------
----------------------------------------------------------------------------------
----------------------------------------------------------------------------------
----------------------------------------------------------------------------------

lift :: Map AtomicProgram [AtomicProgram] -> Kat -> Kat
lift alt KZero = KZero
lift alt KEpsilon = KEpsilon
lift alt (KTest t) = KTest t
lift alt (KVar a) = case a `Map.lookup` alt of
  Nothing -> KVar a
  Just as -> foldr (KUnion . KVar ) KZero as
lift alt (KSeq k k') = lift alt k `KSeq` lift alt k'
lift alt (KUnion k k') = lift alt k `KUnion` lift alt k'
lift alt (KStar k) = KStar $ lift alt k


katOfQuery :: Context -> Query -> [Kat]
katOfQuery ctx QEmpty = [KZero]
katOfQuery ctx QEpsilon = [KEpsilon]
katOfQuery ctx QAll = [foldr (KUnion . KVar) KZero $ atomicActions ctx]
katOfQuery ctx (QIdent s) = [KVar $ AtomicProgram s]
katOfQuery ctx (QApply (QIdent agent) q) =
  case agent `lookup` viewsc ctx of
    Nothing -> error ("Could not find agent \"" ++ agent ++ "\"")
    Just f  -> (lift f) `map` katOfQuery ctx q
katOfQuery ctx (QApply _ _) = error "function application must be with an agent"
katOfQuery ctx (QConcat q q') =
  concatMap (\k -> KSeq k `map` katOfQuery ctx q') (katOfQuery ctx q)
katOfQuery ctx (QUnion q q') =
  concatMap (\k -> (KUnion k `map` katOfQuery ctx q')) (katOfQuery ctx q)
katOfQuery ctx (QIntersect q q') = katOfQuery ctx q ++ katOfQuery ctx q'
katOfQuery ctx (QStar q) = KStar `map` katOfQuery ctx q
katOfQuery ctx (QComplement q) = negate ctx `concatMap` katOfQuery ctx q

negate :: Context -> Kat -> [Kat] 
negate ctx KZero = [Set.fold (KUnion . KVar) KZero $ atomicActions ctx]
negate ctx KEpsilon = [KZero]
negate ctx (KVar a) = [Set.fold (KUnion . KVar) KZero $
                       Set.delete a $ atomicActions ctx]
negate ctx (KTest t) = [KTest $ TNeg t]
negate ctx (KSeq k k') =
  let neg nk nk' = KSeq nk k' `KUnion` KSeq k nk' in
  concatMap (\nk -> (map (neg nk) (negate ctx k'))) $ negate ctx k
negate ctx (KUnion k k') = negate ctx k ++ negate ctx k'
negate ctx (KStar _ ) = [KZero]

mkAutoL' :: Context -> Kat -> Auto [State Atom Kat]
mkAutoL' ctx = mkAutoL (atomsc ctx) (Set.toList $ atomicActions ctx)


compile :: Context -> Query -> Auto [State Atom Kat]
compile ctx query =
  foldr1 intersectAutoL $
  mkAutoL' ctx `map`
  desugar ctx query
  
desugar :: Context -> Query -> [Kat]
desugar ctx query =
  map (substActions (actionsc ctx))
  $ nub $ katOfQuery ctx query

allEqual :: Eq a => [a] -> Maybe a
allEqual [] = Nothing
allEqual [x] = Just x
allEqual (x:x':xs) | x == x' = allEqual (x':xs)
                   | otherwise  = Nothing



allEqual' :: Eq a => [a] -> Maybe [a]
allEqual' [] = Nothing
allEqual' [x] = Just [x]
allEqual' (x:x':xs) | x == x' = allEqual' (x':xs) >>= Just . ((:) x)
                   | otherwise  = Nothing

intersectLazy :: Eq a => [[a]] -> [a]
intersectLazy = (mapMaybe allEqual) . choices

intersectLazy' :: Eq a => [[a]] -> [a]
intersectLazy' = (mapMaybe headMaybe) . foldr ((mapMaybe (allEqual' . uncurry (:)) .) . (+*+)) [[]]
  where headMaybe [] = Nothing
        headMaybe (x:_) = Just x

computeGuardedStrings :: Context -> Query -> [GuardedString]
computeGuardedStrings ctx query =
  let kats = desugar ctx query in
  if null kats then [] else 
  intersectLazy' $
  map (gs_interp $ atomsc ctx)
  kats


injectProg :: AtomicProgram -> (Atom, Atom) -> Kat
injectProg a (pre, post) =
  KTest (testOfAtom pre) `KSeq` KVar a `KSeq` KTest (testOfAtom post)

substActions :: [Action] -> Kat -> Kat
substActions actions KZero = KZero
substActions actions KEpsilon = KEpsilon
substActions actions (KTest t) =  KTest t
substActions actions (KVar p) =
  case p `lookupAction` actions of
    Nothing -> (KVar p)
    Just a  -> program a
substActions actions (KSeq k k') =
  substActions actions k `KSeq`
  substActions actions k'
substActions actions (KUnion k k') =
  substActions actions k `KUnion`
  substActions actions k'
substActions actions (KStar k) =
  KStar $ substActions actions k


