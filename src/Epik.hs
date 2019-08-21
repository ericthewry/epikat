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

data Context =
  Context { alphabetc :: Set AtomicTest
          , assertion :: Test
          , actionsc :: [Action]
          , viewsc :: [(Agent, Map AtomicProgram [AtomicProgram])]}


instance Show Context where
  show ctx = "Context { alphabetc = " ++ show (alphabetc ctx)
             ++ ", actionsc = " ++ show (actionsc ctx)
             ++ ", viewsc = [" ++ intercalate ", " (map (\(agent, _) -> agent ++ " : <func>") (viewsc ctx)) ++ "]"
  
data Action = Action { name :: AtomicProgram
                     , relation :: Set (Atom, Atom)
                     } deriving (Eq, Show)

nameStr :: Action -> String
nameStr = show . name

-- data QueryResult =
--   QAuto Auto 
--   | QRel (Query -> Query)

-- instance Show QueryResult where
--   show (QAuto auto) = show auto
--   show (QRel _) = "<FUN>"

-- gs_relation :: (Ord a, Ord b) =>
--                (GuardedString -> a) ->
--                (GuardedString -> b) ->
--                Set GuardedString    -> Set (a,b)
-- gs_relation f g = Set.map (\s -> (f s, g s)) 

-- compile_action :: AtomicProgram -> Set AtomicTest -> [Test] -> Kat -> Action
-- compile_action name alphabet assertions kat_term =
--   Action { name = name
--          , relation = gs_relation first last $
--                       gs_assertion_interp alphabet (foldr TAnd TTrue assertions) kat_term
--          }


-- project_trans_list :: AtomicProgram -> [AtomicProgram] -> (Cond, Integer) -> [(Cond, Integer)] -> [(Cond, Integer)]
-- project_trans_list _ _ (CTest t,next_hop) rst = (CTest t, next_hop) : rst
-- project_trans_list trueAct actAlts (CProg p,next_hop) rst  =
--   if p == trueAct then
--     foldr (\a -> (:) (CProg a, next_hop)) rst actAlts
--   else
--     (CProg p, next_hop) : rst    

-- projectAuto :: AtomicProgram -> [AtomicProgram] -> Auto -> Auto
-- projectAuto trueAct actAlts auto =
--   let delta' =
--         Map.foldrWithKey (\state transitions ->
--                             Map.insert state
--                             (foldr (project_trans_list trueAct actAlts) [] transitions)
--                          ) Map.empty (delta auto) in
--   Auto { start = start auto
--        , delta = delta'
--        , final = final auto}
        
-- binary combine recFun left right = (recFun left) `combine` (recFun right)

-- compileView :: Map AtomicProgram [AtomicProgram] -> Query -> Query
-- compileView _ QEmpty = QEmpty
-- compileView _ QEpsilon = QEpsilon
-- compileView _ QAll = QAll
-- compileView view (QIdent s) =
--   case AtomicProgram s `Map.lookup` view of
--     Nothing -> QIdent s
--     Just [] -> QIdent s
--     Just alts ->
--       foldr (QUnion . QIdent . show ) QEmpty alts
    
-- compileView view (QApply q q') =
--   binary QApply (compileView view) q q'

-- compileView view (QConcat q q') =
--   binary QConcat (compileView view) q q'

-- compileView view (QUnion q q') =
--   binary QUnion (compileView view) q q'

-- compileView view (QComplement q) =
--   QComplement $ compileView view q

-- compileView view (QStar q) =
--   QStar $ compileView view q


-- lookupAction :: AtomicProgram -> [Action] -> Maybe Action
-- lookupAction p = find (\a -> name a == p)

-- testFromAtom :: Atom -> Test
-- testFromAtom atom =
--   let toTest c p = Set.fold (TAnd . c . TVar) TTrue $ p atom in
--     toTest id posa `TAnd` toTest TNeg nega

-- katFromAtom :: Atom -> Kat
-- katFromAtom = KTest . testFromAtom

-- katFromAction :: Action -> Kat
-- katFromAction act = Set.foldr (\(pre, post) kat ->
--                                  katFromAtom pre `KSeq`
--                                  KVar (name act) `KSeq`
--                                  katFromAtom post `KUnion` kat
--                               ) KZero (relation act)

-- scopeFor :: [(QueryName, Query)] -> QueryName -> [(QueryName, Query)]
-- scopeFor qs name = takeWhile (\(n, _) -> n /= name) qs

atomicActions :: Context -> Set AtomicProgram
atomicActions ctx = foldr (\x -> Set.insert (name x)) Set.empty (actionsc ctx)

atoms :: Context -> [Atom]
atoms ctx = induced_atoms (alphabetc ctx) $ assertion ctx

-- compileQuery :: Context -> Query -> QueryResult
-- compileQuery _ QEmpty = QAuto $ construct KZero
-- compileQuery _ QEpsilon = QAuto $ construct KEpsilon
-- compileQuery ctx QAll = compileQuery ctx $
--                         foldr (QUnion . QIdent . nameStr) QEpsilon $
--                         actionsc ctx

-- compileQuery ctx (QIdent s) =
--   case (AtomicProgram s `lookupAction` actionsc ctx, s `lookup` (viewsc ctx)) of
--     (Just a, Nothing) -> QAuto $ construct $ katFromAction a
--     (Nothing, Just f) -> QRel f
--     (Nothing, Nothing) -> error ("UseBeforeDef. Could not find name " ++ s)
--     (_, _) -> error ("Error. I found both an Agent and an Action with name " ++ s ++ ". Please resolve this ambiguity. By convention, actions should be in snake_case, and agents should be in full CamelCase")
    
-- compileQuery ctx (QApply q q') =
--   case (compileQuery ctx q) of
--     (QAuto _) -> error "Type Error: Cannot Apply an Automaton as a function"
--     (QRel f) -> compileQuery ctx $ f q'
    
-- compileQuery ctx (QConcat q q') =
--   case (compileQuery ctx q, compileQuery ctx q') of
--     (QAuto a, QAuto a') -> QAuto (a `concatAuto` a')
--     (QRel f, QRel f') -> QRel (\x -> f x `QConcat` f' x)
--     (QRel _, QAuto _) -> error "cannot concat a function and an automaton"
--     (QAuto _, QRel _) -> error "cannot concat an automaton and a function"

-- compileQuery ctx (QUnion q q') =
--   case (compileQuery ctx q, compileQuery ctx q') of
--     (QAuto a, QAuto a') -> QAuto (a `unionAuto` a')
--     (QRel f, QRel f') -> QRel (\x -> f x `QUnion` f' x)
--     (_, _) -> error "Cannot union a function and an automaton"
     
-- compileQuery ctx (QIntersect q q') =
--   -- Intersection is defined directly
--   -- case (compileQuery ctx q, compileQuery ctx q') of
--   --   (QAuto a, QAuto a') -> QAuto $ intersectAuto (atomicActions ctx) a a'
--   --   (QRel f, QRel f') -> QRel (\x -> f x `QIntersect` f' x)
--   --   (_, _) -> error "Cannot intersect a function and an automaton"
--   -- intersection is syntactic sugar
--   compileQuery ctx $
--   QComplement $ QComplement q `QUnion` QComplement q'

-- -- compileQuery ctx (QComplement QEmpty) = compileQuery ctx QAll
-- -- compileQuery ctx (QComplement QEpsilon) = compileQuery ctx $ QAll `QUnion` QEmpty
-- -- compileQuery ctx (QComplement QAll) = compileQuery ctx QEmpty
-- -- compileQuery ctx (QComplement QComplement q) = compileQuery ctx q
-- -- compileQuery ctx (QComplement QStar x) = 
-- compileQuery ctx (QComplement q) =  
--   case compileQuery ctx q of
--     QAuto a -> QAuto $
--                construct (KTest $ assertion ctx)
--                `concatAuto`
--                complementAuto (atomicActions ctx) a
--                `concatAuto`
--                construct (KTest $ assertion ctx)
               
--     QRel f -> QRel $ (\q -> QComplement $ f q)

-- -- compileQuery ctx (QSubtract q q') = compileQuery ctx $
-- --                                     q `QIntersect` QComplement q'
  
-- compileQuery ctx (QStar q) =
--   case compileQuery ctx q of
--     QAuto a -> QAuto $ iterateAuto a
--     QRel f -> QRel (\x -> QStar $ f x)


-- mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
-- mapSnd f = map (\(x, y) -> (x, f y))
  
-- compileDecls :: Declarations -> Context
-- compileDecls (Program alphabet asserts actions views queries) =
--   Context { alphabetc = alphabet
--           , assertion = foldr TAnd TTrue asserts
--           , actionsc = map (\(n, p) -> compile_action n alphabet asserts p) actions
--           , viewsc = mapSnd (compileView) views
--           }
-- binOp f c x y = c (f x) (f y)
-- unOp f c x = c $ f x

-- resolveRefs :: [(QueryName, Query)] -> Query -> Query
-- resolveRefs scope QEmpty = QEmpty
-- resolveRefs scopre QEpsilon = QEpsilon
-- resolveRefs scope QAll = QAll
-- resolveRefs scope (QIdent s) =
--   case s `lookup` scope  of
--     Nothing -> QIdent s
--     Just q -> q
-- resolveRefs scope (QApply f x) =
--   binOp (resolveRefs scope) QApply f x
-- resolveRefs scope (QConcat q q') =
--   binOp (resolveRefs scope) QConcat q q'
-- resolveRefs scope (QUnion q q') =
--   binOp (resolveRefs scope) QUnion q q'
-- resolveRefs scope (QIntersect q q') =
--   binOp (resolveRefs scope) QIntersect q q'
-- resolveRefs scope (QComplement q) =
--   unOp (resolveRefs scope) QComplement q
-- resolveRefs scope (QStar q) =
--   unOp (resolveRefs scope) QStar q
  

-- runQueries :: Declarations -> [(QueryName, QueryResult)]
-- runQueries decls =
--   let context = compileDecls decls in
--   let qs = queries decls in
--   map (\(name, q) -> (name, compileQuery context $ resolveRefs (scopeFor qs name) q)) qs

-- accShow :: Show a => String -> a -> String -> String
-- accShow sep x str = sep ++ show x ++ str

-- showQueryResults :: Declarations -> String
-- showQueryResults decls =
--   let queries = runQueries decls in
--     foldr (\(name,res) accStr ->
--               case res of
--                 QRel _ -> name ++ " is a function, so we cannot print it"
--                 QAuto a ->
--                   let guardedStrings = foldr (accShow "\n\t") "\n" $
--                                        nub $
--                                        toLoopFreeStrings (alphabet decls) a  in
--                   name ++ " identifies the following (loop-free) strings:" ++ guardedStrings ++  "-----\n\n" ++ accStr
--                   -- name ++ " produces the automaton: \n " ++ show a ++ "----\n\n" ++ accStr
--           ) "" queries



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
  Just as -> foldr (KUnion . KVar ) KEpsilon as
lift alt (KSeq k k') = lift alt k `KSeq` lift alt k'
lift alt (KUnion k k') = lift alt k `KUnion` lift alt k'
lift alt (KStar k) = KStar $ lift alt k


katOfQuery :: Context -> Query -> [Kat]
katOfQuery ctx QEmpty = [KZero]
katOfQuery ctx QEpsilon = [KEpsilon]
katOfQuery ctx QAll = [foldr (KUnion . KVar) KEpsilon $ atomicActions ctx]
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
negate ctx KZero = [Set.fold (KUnion . KVar) KEpsilon $ atomicActions ctx]
negate ctx KEpsilon = [KZero]
negate ctx (KVar a) = [Set.fold (KUnion . KVar) KEpsilon $ Set.delete a $ atomicActions ctx]
negate ctx (KTest t) = [KTest $ TNeg t]
negate ctx (KSeq k k') =
  let neg nk nk' = KSeq nk k' `KUnion` KSeq k nk' in
  concatMap (\nk -> (map (neg nk) (negate ctx k'))) $ negate ctx k
negate ctx (KUnion k k') = negate ctx k ++ negate ctx k'
negate ctx (KStar _ ) = [KZero]


compile :: Context -> Query -> Auto [State Atom Kat]
compile ctx q =
  foldr1 intersectAutoL $
  mkAutoL (atoms ctx) (Set.toList $ atomicActions ctx)  `map`
  katOfQuery ctx q
