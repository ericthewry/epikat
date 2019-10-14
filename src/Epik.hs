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
                     , program :: Kat AtomicProgram
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
          , viewsc :: [(Agent, Map AtomicProgram [AtomicProgram])]
          , queriesc :: QueryData}


instance Show Context where
  show ctx = "Context { alphabetc = " ++ show (alphabetc ctx)
             ++ ", actionsc = " ++ show (actionsc ctx)
             ++ ", viewsc = [" ++ intercalate ", " (map (\(agent, _) -> agent ++ " : <func>") (viewsc ctx)) ++ "]"




compileAction :: AtomicProgram -> Kat AtomicProgram -> Action
compileAction name k =
  Action { name = name, program = subst (AtomicProgram "id") name k }

-- substiutes every occurence of obs for rplc in kat expr
subst obs rplc KZ = kzero
subst obs rplc KEps = kepsilon
subst obs rplc (KBool t) = ktest t
subst obs rplc (KEvent x) | obs == x = kvar rplc
                        | otherwise = kvar x
subst obs rplc (KSequence k k') =
  subst obs rplc k `kseq` subst obs rplc k' 
subst obs rplc (KPlus k k') =
  subst obs rplc k `kunion` subst obs rplc k'
subst obs rplc (KAnd k k') =
  subst obs rplc k `kand` subst obs rplc k'
subst obs rplc (KIter k) =
  kstar $ subst obs rplc k



compileDecls :: Declarations -> Context
compileDecls (Program alphabet asserts actions views queries) =
  let assertion = foldr TAnd TTrue asserts in
  let atoms = inducedAtoms assertion $ allAtoms alphabet in
  Context { alphabetc = alphabet
          , atomsc = atoms
          , assertion = assertion
          , actionsc = map (\(n, p) -> compileAction n p) actions
          , viewsc = views
          , queriesc = queries
          
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
  map (\(n, c, q) -> (n, c, gs_interpQ context q)) $
--  map (\(n, c, q) -> (n, c,computeGuardedStrings context (scopeFor (queries decls) n) q)) $
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
  -- let queries = if useStrings then runQueries decls else runQueriesAuto decls in
  let queries = runQueries decls in
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

lift :: Ord p => Map p [p] -> Kat p -> Kat p
lift alt KZ = kzero             
lift alt KEps = kepsilon
lift alt (KBool t) = ktest t
lift alt (KEvent a) = case a `Map.lookup` alt of
  Nothing -> kvar a
  Just as -> foldr (kunion . kvar ) kzero as
lift alt (KSequence k k') = lift alt k `kseq` lift alt k'
lift alt (KPlus k k') = lift alt k `kunion` lift alt k'
lift alt (KIter k) = kstar $ lift alt k

liftQ :: Map AtomicProgram [AtomicProgram] -> Query -> Query
liftQ alt QEmpty = QEmpty  
liftQ alt QAll = QAll
liftQ alt QEpsilon = QEpsilon
liftQ alt (QTest t) = QTest t
liftQ alt (QIdent a) = case (AtomicProgram a) `Map.lookup` alt of
  Nothing -> QIdent a
  Just as -> foldr (QUnion . QIdent . show ) QEmpty as
liftQ alt q@(QApply _ _) = error ("nested QApply could not be resolved for expr " ++ show q)
liftQ alt (QConcat q q') = liftQ alt q `QConcat` liftQ alt q'
liftQ alt (QUnion q q') = liftQ alt q `QUnion` liftQ alt q'
liftQ alt (QIntersect q q') = liftQ alt q `QIntersect` liftQ alt q'
liftQ alt (QComplement q) = QComplement $ liftQ alt q
liftQ alt (QStar k) = QStar $ liftQ alt k

liftGS :: Context -> Map AtomicProgram [AtomicProgram] -> GuardedString -> [GuardedString]
liftGS ctx alt (Single atom) = [Single atom]
liftGS ctx alt gs'@(Prog atom p gs) =
  case (p `Map.lookup` alt) of
    Nothing -> [gs']
    Just alts ->
      let katOfProg s = s `lookupAction` actionsc ctx in
      let altA = mapMaybe katOfProg alts in
      let altQ = map (queryOfKat . program) altA in        
      let altGS = concatMap (gs_interpQ ctx) altQ in
      -- error ((show [Single atom]) ++ " <> " ++ (show p) ++ " <> " ++ show (liftGS ctx alt gs) ++ " ==== " ++ show (
        if gsLen gs == 0 then altGS else 
          altGS +<>+ liftGS ctx alt gs
            -- ))

invert :: Map AtomicProgram [AtomicProgram] -> Map AtomicProgram [AtomicProgram]
invert =
  Map.foldrWithKey'
  (\k vs m' ->
     foldr (\v -> Map.insertWith (++) v [k]) m' vs
  ) Map.empty  

liftGSPre :: Context -> Map AtomicProgram [AtomicProgram] -> GuardedString -> [GuardedString]
liftGSPre ctx alt = liftGS ctx (invert alt)


lookupQ :: String -> QueryData -> Maybe Query
lookupQ n [] = Nothing
lookupQ n ((n', _, q):qs) = if n == n' then Just q
                            else lookupQ n qs


queryOfKat :: Show p => Kat p -> Query
queryOfKat KZ = QEmpty
queryOfKat KEps = QEpsilon
queryOfKat (KBool t) =  QTest t
queryOfKat (KEvent a) = QIdent $ show a
queryOfKat (KSequence k k') = binop queryOfKat QConcat k k'
queryOfKat (KPlus k k') = binop queryOfKat QUnion k k'
queryOfKat (KAnd k k') = binop queryOfKat QIntersect k k'
queryOfKat (KIter k) = QStar $ queryOfKat k

katOfQuery :: Context -> QueryData ->  Query -> [Kat AtomicProgram]
katOfQuery ctx scope QEmpty = [kzero]
katOfQuery ctx scope QEpsilon = [kepsilon]
katOfQuery ctx scope QAll = [Set.foldr (kunion . kvar) kzero $ atomicActions ctx]
katOfQuery ctx scope (QIdent s) =
  case s `lookupQ` scope  of
    Just q  -> katOfQuery ctx scope q
    Nothing -> [kvar $ AtomicProgram s]
katOfQuery ctx scope (QTest t) = [ktest t]
katOfQuery ctx scope (QApply (QIdent agent) q) =
  case agent `lookup` viewsc ctx of
    Nothing -> error ("Could not find agent \"" ++ agent ++ "\"")
    Just f  -> [ kapply (lift f) k | k <- katOfQuery ctx scope q ]
               -- lift f `map` katOfQuery ctx scope q
katOfQuery ctx scope (QApply _ _) = error "function application must be with an agent"
katOfQuery ctx scope (QConcat q q') =
  [kseq k k' | k <- katOfQuery ctx scope q, k' <- katOfQuery ctx scope q' ]
katOfQuery ctx scope (QUnion q q') =
  [ kunion k k' | k <- katOfQuery ctx scope q, k' <- katOfQuery ctx scope q']
katOfQuery ctx scope (QIntersect q q') =
  [ kand k k' | k <- katOfQuery ctx scope q, k' <- katOfQuery ctx scope q']
katOfQuery ctx scope (QStar q) =
  [ kstar k | k <- katOfQuery ctx scope q ]
katOfQuery ctx scope (QComplement q) =
  [ kneg k | k <- katOfQuery ctx scope q]
  
--  concatMap (\k -> map (kunion k) (katOfQuery ctx scope $ QConcat q $ QConcat QAll $ QStar QAll)) $
  -- case q of
  --   QAll -> [kzero]
  --   QEpsilon ->  [kzero]
  --   QEmpty -> [kepsilon]
  --   QComplement q -> katOfQuery ctx scope q
  --   QTest t -> [ktest $ TNeg t]
  --   QIdent s -> case s `lookupQ` scope  of
  --                 Just q  -> katOfQuery ctx scope q
  --                 Nothing -> [Set.fold (kunion . kvar) kzero $
  --                             Set.delete (AtomicProgram s) $ atomicActions ctx]
  --   (QApply (QIdent agent)  q') ->
  --     case agent `lookup` viewsc ctx of
  --       Nothing -> error ("Could not find agent \"" ++ agent ++ "\"")
  --       Just f  -> concatMap ((katOfQuery ctx scope) . QComplement . queryOfKat . (lift f)) $ katOfQuery ctx scope q'
  --   (QApply q _ ) -> error ("LHS of application must be agent, not " ++ show q)
  --   QUnion q q' -> katOfQuery ctx scope $
  --                  QIntersect (QComplement q) (QComplement q')
  --   QConcat q q' -> katOfQuery ctx scope $
  --                   QUnion (QConcat (QComplement q) q') $
  --                   QUnion (QConcat q $ QComplement q') $
  --                   QConcat (QComplement q) (QComplement q')

  --   QIntersect q q' -> katOfQuery ctx scope $
  --                      QUnion (QComplement q) (QComplement q')
  --   QStar q -> [kzero]

mkAutoL' :: Context -> Kat AtomicProgram -> Auto [State Atom (Kat AtomicProgram)]
mkAutoL' ctx = mkAutoL (atomsc ctx) (Set.toList $ atomicActions ctx)


compile :: Context -> QueryData -> Query -> Auto [State Atom (Kat AtomicProgram)]
compile ctx scope query =
  foldr1 intersectAutoL $
  mkAutoL' ctx `map`
  desugar ctx scope query

fstApply :: (a -> b) -> (a,c) -> (b, c)
fstApply f (x, y) = (f x, y)
  
desugar :: Context -> QueryData -> Query -> [Kat AtomicProgram]
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

unroll :: Int -> Kat p -> Kat p
unroll 0 k = k
unroll _ KZ = kzero
unroll _ KEps = kepsilon
unroll _ (KEvent v) = kvar v
unroll _ (KBool t) = ktest t
unroll n (KSequence k k') = unroll n k `kseq` unroll n k'
unroll n (KPlus k k') = unroll n k `kunion` unroll n k'
unroll n (KIter k) =
  let k' = unroll n k in
    kunion kepsilon $ kseq k' $ unroll (n-1) $ kstar k'

computeGuardedStrings :: Context -> QueryData -> Query -> [GuardedString]
computeGuardedStrings ctx scope query =
--  let (unionKat, andKats) = desugar ctx scope query in
  let kats = desugar ctx scope query in
  let denote = gs_interp $ atomsc ctx in
  -- denote unionKat ++ 
  (intersectLazy' $
   map (denote . (unroll 6)) kats)


injectProg :: AtomicProgram -> (Atom, Atom) -> Kat AtomicProgram
injectProg a (pre, post) =
  ktest (testOfAtom pre) `kseq` kvar a `kseq` ktest (testOfAtom post)

substActions :: [Action] -> Kat AtomicProgram -> Kat AtomicProgram
substActions actions KZ = kzero
substActions actions KEps = kepsilon
substActions actions (KBool t) =  ktest t
substActions actions (KEvent p) =
  case p `lookupAction` actions of
    Nothing -> (kvar p)
    Just a  -> program a
substActions actions (KSequence k k') =
  substActions actions k `kseq`
  substActions actions k'
substActions actions (KPlus k k') =
  substActions actions k `kunion`
  substActions actions k'
substActions actions (KAnd k k') =
  substActions actions k `kand`
  substActions actions k'
substActions actions (KIter k) =
  kstar $ substActions actions k

gs_interpQ :: Context -> Query -> [GuardedString]
gs_interpQ ctx QEmpty = []
gs_interpQ ctx QEpsilon = [(Single a) | a <- atomsc ctx]
gs_interpQ ctx QAll = concatMap ((gs_interpQ ctx) . queryOfKat . program) $ actionsc ctx
gs_interpQ ctx (QTest t) =
  [(Single a) | a <- atomsc ctx, eval (atomToWorld a) t]
gs_interpQ ctx (QIdent s) =
  case AtomicProgram s `lookupAction` actionsc ctx of
    Just x -> gs_interp (atomsc ctx) $ program x
    Nothing -> case s `lookupQ` queriesc ctx of
                 Just q -> gs_interpQ ctx q
                 Nothing -> error ("USEBEFOREDEF " ++ s)

gs_interpQ ctx q'@(QApply (QIdent s) q) =
  case s `lookup` viewsc ctx of
    Just f -> liftGSPre ctx f `concatMap` gs_interpQ ctx q
      -- error ( s ++ "(" ++ (show q) ++ ") == "
      --        ++ show (take 20 $ liftGS ctx f `concatMap` gs_interpQ ctx q))
    Nothing -> error ("LHS of apply must be agent, could not find agent called" ++ s)

gs_interpQ ctx (QApply _ _ ) = error ("LHS of apply must be agent, not query")

gs_interpQ ctx (QConcat q q') = gs_interpQ ctx q `listFuse` gs_interpQ ctx q'
gs_interpQ ctx (QUnion q q') = gs_interpQ ctx q +++ gs_interpQ ctx q'
gs_interpQ ctx (QIntersect q q') =
  interPairList (gs_interpQ ctx q +*+ gs_interpQ ctx q')
gs_interpQ ctx (QComplement q) =
  gs_interpQ ctx (QAll `QConcat` QStar QAll) +-+ gs_interpQ ctx q
gs_interpQ ctx (QStar q) = fixpointGS (atomsc ctx) $ gs_interpQ ctx q

interPairList :: Eq a => [(a,a)] -> [a]
interPairList [] = []
interPairList ((a,a'):as) | a == a' = a : interPairList as
                          | otherwise = interPairList as
