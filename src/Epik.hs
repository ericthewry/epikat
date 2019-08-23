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

scopeFor :: QueryData -> QueryName -> QueryData
scopeFor qs name = takeWhile (\(n, _, _) -> n /= name) qs

atomicActions :: Context -> Set AtomicProgram
atomicActions ctx = foldr (\x -> Set.insert (name x)) Set.empty (actionsc ctx)

-- atomsCtx :: Context -> [Atom]
-- atomsCtx ctx = inducedAtoms (assertion ctx) $ allAtoms (alphabetc ctx)

runQueries :: Declarations -> [(QueryName, String, [GuardedString])]
runQueries decls =
  let context = compileDecls decls in
  map (\(n, c, q) -> (n, c, computeGuardedStrings context (scopeFor (queries decls) n) q)) $
  queries decls

runQueriesAuto :: Declarations -> [(QueryName, String, [GuardedString])]
runQueriesAuto decls =
  let ctx = compileDecls decls in
    map (\(n,c,q) -> (n, c,
                      mapMaybe id $ Set.toList $
                      loopFreeStrings $ (compile ctx $ scopeFor (queries decls) n) q)) $
    queries decls

mapSnd :: (a -> b -> c) -> [(a,b)] -> [(a,c)]
mapSnd _ [] = []
mapSnd f ((x,y):xs) = (x, f x y) : mapSnd f xs
  

accShow :: Show a => String -> a -> String -> String
accShow sep x str = sep ++ show x ++ str

showQueryResults :: Int -> Bool -> Declarations -> String
showQueryResults num useStrings decls =
  let queries = if useStrings then runQueries decls else runQueriesAuto decls in
    foldr (\(name, comments, gsTraces) accStr ->
                let gsStr = foldr (accShow "\n\t") "\n" (sortOn gsLen$ takeUnique num gsTraces)  in
                let header = name ++ " identifies the following strings:" in
                let footer = replicate (length header `div` 2) '+' in
                  comments ++ "\n" ++ 
                  header ++ "\n" ++
                  gsStr ++ "\n" ++ 
                  footer ++ "\n\n" ++ accStr
             -- name ++ " produces the automaton: \n " ++ show auto ++ "----\n\n" ++ accStr
          ) "" queries

showKatTerms :: Declarations -> String
showKatTerms decls =
  let ctx = compileDecls decls in
    concatMap (\(n, cs, aks) -> cs ++ "\n" ++ n ++ " becomes KAT expressions: \n" ++
                -- "\t" ++ show ukat ++ "\n\t+\n" ++
                concatMap (\k -> "\t" ++ show k ++ "\n") aks ++ "\n") $
    map (\(n,c, q) -> ( n, c, desugar ctx (scopeFor (queries decls) n) q)) $ queries decls



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

lookupQ :: String -> QueryData -> Maybe Query
lookupQ n [] = Nothing
lookupQ n ((n', _, q):qs) = if n == n' then Just q
                            else lookupQ n qs

katOfQuery :: Context -> QueryData ->  Query -> [Kat]
katOfQuery ctx scope QEmpty = [KZero]
katOfQuery ctx scope QEpsilon = [KEpsilon]
katOfQuery ctx scope QAll = [Set.foldr (KUnion . KVar) KZero $ atomicActions ctx]
katOfQuery ctx scope (QIdent s) =
  case s `lookupQ` scope  of
    Just q  -> katOfQuery ctx scope q
    Nothing -> [KVar $ AtomicProgram s]
katOfQuery ctx scope (QTest t) = [KTest t]
katOfQuery ctx scope (QApply (QIdent agent) q) =
  case agent `lookup` viewsc ctx of
    Nothing -> error ("Could not find agent \"" ++ agent ++ "\"")
    Just f  -> (lift f) `map` katOfQuery ctx scope q -- lift this to operate on Queries
katOfQuery ctx scope (QApply _ _) = error "function application must be with an agent"
katOfQuery ctx scope (QConcat q q') =
  concatMap (\k -> KSeq k `map` katOfQuery ctx scope q') (katOfQuery ctx scope q)
katOfQuery ctx scope (QUnion q q') =
  concatMap (\k -> (KUnion k `map` katOfQuery ctx scope q')) (katOfQuery ctx scope q)
katOfQuery ctx scope (QIntersect q q') =
  katOfQuery ctx scope q ++ katOfQuery ctx scope q'
katOfQuery ctx scope (QStar q) =
    KStar `map` katOfQuery ctx scope q
katOfQuery ctx scope (QComplement q) =
  case q of
    QAll -> [KZero]
    QEpsilon ->  [KZero]
    QEmpty -> [KEpsilon]
    QComplement q -> katOfQuery ctx scope q
    QTest t -> [KTest $ TNeg t]
    QIdent s -> case s `lookupQ` scope  of
                  Just q  -> katOfQuery ctx scope q
                  Nothing -> [Set.fold (KUnion . KVar) KZero $
                              Set.delete (AtomicProgram s) $ atomicActions ctx]
                             
    q@(QApply _ _) ->  negate ctx `concatMap` katOfQuery ctx scope q
    QUnion q q' -> katOfQuery ctx scope (QComplement q) `union`
                   katOfQuery ctx scope (QComplement q')
    QConcat q q' -> uncurry (KUnion . uncurry KUnion) `map`
                    ((katOfQuery ctx scope (QComplement q `QConcat` q')
                     +*+
                     katOfQuery ctx scope (q `QConcat` QComplement q'))
                     +*+
                     katOfQuery ctx scope (QComplement q `QConcat` QComplement q')
                    )
    QIntersect q q' -> uncurry KUnion `map`
                       (katOfQuery ctx scope (QComplement q)
                        +*+
                        katOfQuery ctx scope (QComplement q'))
    QStar q -> [KZero]
-- katOfQuery ctx scope (QComplement q) = negate ctx `concatMap` katOfQuery ctx scope q

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


compile :: Context -> QueryData -> Query -> Auto [State Atom Kat]
compile ctx scope query =
  foldr1 intersectAutoL $
  mkAutoL' ctx `map`
  desugar ctx scope query

divideUnions :: Kat -> [Kat]
divideUnions (KUnion k KZero) = divideUnions k
divideUnions (KUnion KZero k') = divideUnions k'
divideUnions (KUnion k k') = divideUnions k ++ divideUnions k'
divideUnions k = [k]

restoreUnions :: Set Kat -> Kat
restoreUnions = Set.fold (KUnion) KZero

factorUnions :: [Set Kat] -> (Set Kat, [[Kat]])
factorUnions ks =
  let commonUnions = foldr1 Set.intersection ks in
  let remainder = map (\us -> Set.toList (us `Set.difference` commonUnions)) ks in
  (commonUnions, remainder)

fstApply :: (a -> b) -> (a,c) -> (b, c)
fstApply f (x, y) = (f x, y)
  
desugar :: Context -> QueryData -> Query -> [Kat]
desugar ctx scope query =
  -- factorUnions $
  -- map divideUnions $ -- [Set Kat]
  map (substActions (actionsc ctx)) $ -- [Kat]
  nub $
  katOfQuery ctx scope query

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

unroll :: Int -> Kat -> Kat
unroll 0 k = k
unroll _ KZero = KZero
unroll _ KEpsilon = KEpsilon
unroll _ (KVar v) = KVar v
unroll _ (KTest t) = KTest t
unroll n (KSeq k k') = unroll n k `KSeq` unroll n k'
unroll n (KUnion k k') = unroll n k `KUnion` unroll n k'
unroll n (KStar k) =
  let k' = unroll n k in
    KUnion KEpsilon $ KSeq k' $ unroll (n-1) $ KStar k'

computeGuardedStrings :: Context -> QueryData -> Query -> [GuardedString]
computeGuardedStrings ctx scope query =
--  let (unionKat, andKats) = desugar ctx scope query in
  let kats = desugar ctx scope query in
  let denote = gs_interp $ atomsc ctx in
  -- denote unionKat ++ 
  (intersectLazy' $
   map (denote . (unroll 6)) kats)


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


