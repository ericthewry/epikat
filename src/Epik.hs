module Epik where

import Prelude hiding (last, negate)

import Data.List hiding (last)

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import qualified Data.Either as Either

{- INTERNAL MODULES -}
import Syntax
import GuardedStrings
import BDD
import AutoDeriv
{- END INTERNAL MODULES -}
  
data Action = Action { name :: AtomicProgram
                     , relation :: Set (Atom, Atom)
                     } deriving (Eq, Show)

nameStr :: Action -> String
nameStr = show . name

lookupAction :: AtomicProgram -> [Action] -> Maybe Action
lookupAction p = find (\a -> name a == p)

  
data Context =
  Context { alphabetc :: Set AtomicTest
          , assertion :: Test
          , actionsc :: [Action]
          , viewsc :: [(Agent, Map AtomicProgram [AtomicProgram])]}


instance Show Context where
  show ctx = "Context { alphabetc = " ++ show (alphabetc ctx)
             ++ ", actionsc = " ++ show (actionsc ctx)
             ++ ", viewsc = [" ++ intercalate ", " (map (\(agent, _) -> agent ++ " : <func>") (viewsc ctx)) ++ "]"




compileAction :: AtomicProgram -> Set AtomicTest -> Test -> Kat -> Action
compileAction name alphabet assert k =
  Action { name = name
         , relation = Set.map (\s -> (first s, last s)) $
                      gs_assertion_interp alphabet assert k
         }


compileDecls :: Declarations -> Context
compileDecls (Program alphabet asserts actions views queries) =
  let assertion = foldr TAnd TTrue asserts in
  Context { alphabetc = alphabet
          , assertion = assertion
          , actionsc = map (\(n, p) -> compileAction n alphabet assertion p) actions
          , viewsc = views
          }

scopeFor :: [(QueryName, Query)] -> QueryName -> [(QueryName, Query)]
scopeFor qs name = takeWhile (\(n, _) -> n /= name) qs

atomicActions :: Context -> Set AtomicProgram
atomicActions ctx = foldr (\x -> Set.insert (name x)) Set.empty (actionsc ctx)

atoms :: Context -> [Atom]
atoms ctx = induced_atoms (alphabetc ctx) $ assertion ctx  

runQueries :: Declarations -> [(QueryName, Set GuardedString)]
runQueries decls =
  let context = compileDecls decls in
  let qs = queries decls in
  map (\(name, q) -> (name, computeGuardedStrings context q)) qs

accShow :: Show a => String -> a -> String -> String
accShow sep x str = sep ++ show x ++ str

showQueryResults :: Declarations -> String
showQueryResults decls =
  let queries = runQueries decls in
    foldr (\(name, gsTraces) accStr ->
                let gsStr = Set.foldr (accShow "\n\t") "\n" gsTraces  in
                  name ++ " identifies the following (loop-free) strings:\n" ++ gsStr ++  "-----\n\n" ++ accStr
             -- name ++ " produces the automaton: \n " ++ show auto ++ "----\n\n" ++ accStr
          ) "" queries



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
mkAutoL' ctx = mkAutoL (atoms ctx) (Set.toList $ atomicActions ctx)


compile :: Context -> Query -> Auto [State Atom Kat]
compile ctx query =
  foldr1 intersectAutoL $
  mkAutoL' ctx `map`
  desugar ctx query
  
desugar :: Context -> Query -> [Kat]
desugar ctx query =
  map (applyActionConditions (actionsc ctx))
  $ nub $ katOfQuery ctx query


computeGuardedStrings :: Context -> Query -> Set GuardedString
computeGuardedStrings ctx query =
  let kats = desugar ctx query in
  if null kats then Set.empty else 
  foldr1 Set.intersection $
  map (gs_interp $ alphabetc ctx)
  kats


injectProg :: AtomicProgram -> (Atom, Atom) -> Kat
injectProg a (pre, post) =
  KTest (testOfAtom pre) `KSeq` KVar a `KSeq` KTest (testOfAtom post)

applyActionConditions :: [Action] -> Kat -> Kat
applyActionConditions actions KZero = KZero
applyActionConditions actions KEpsilon = KEpsilon
applyActionConditions actions (KTest t) =  KTest t
applyActionConditions actions (KVar p) =
  case p `lookupAction` actions of
    Nothing -> (KVar p)
    Just a  -> Set.foldr (KUnion . injectProg p) KZero (relation a)
applyActionConditions actions (KSeq k k') =
  applyActionConditions actions k `KSeq`
  applyActionConditions actions k'
applyActionConditions actions (KUnion k k') =
  applyActionConditions actions k `KUnion`
  applyActionConditions actions k'
applyActionConditions actions (KStar k) =
  KStar $ applyActionConditions actions k


