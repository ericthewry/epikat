module Epik where

import Prelude hiding (last)

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
import Auto
{- END INTERNAL MODULES -}

data Context =
  Context { alphabetc :: Set AtomicTest
          , actionsc :: [Action]
          , viewsc :: [(Agent, Query -> Query)]}


instance Show Context where
  show ctx = "Context { alphabetc = " ++ show (alphabetc ctx)
             ++ ", actionsc = " ++ show (actionsc ctx)
             ++ ", viewsc = [" ++ intercalate ", " (map (\(agent, _) -> agent ++ " : <func>") (viewsc ctx)) ++ "]"
  
data Action = Action { name :: String
                     , relation :: Set (Atom, Atom)
                     } deriving (Eq, Show)

data QueryResult =
  QAuto Auto
  | QRel (Query -> Query)

instance Show QueryResult where
  show (QAuto auto) = show auto
  show (QRel _) = "<FUN>"


gs_relation :: (Ord a, Ord b) =>
               (GuardedString -> a) ->
               (GuardedString -> b) ->
               Set GuardedString    -> Set (a,b)
gs_relation f g = Set.map (\s -> (f s, g s)) 

compile_action :: String -> Set AtomicTest -> [Test] -> Kat -> Action
compile_action name alphabet assertions kat_term =
  Action { name = name
         , relation = gs_relation first last $
                      gs_assertion_interp alphabet (foldr TAnd TTrue assertions) kat_term
         }


project_trans_list :: AtomicProgram -> [AtomicProgram] -> (Cond, Integer) -> [(Cond, Integer)] -> [(Cond, Integer)]
project_trans_list _ _ (CTest t,next_hop) rst = (CTest t, next_hop) : rst
project_trans_list trueAct actAlts (CProg p,next_hop) rst  =
  if p == trueAct then
    foldr (\a -> (:) (CProg a, next_hop)) rst actAlts
  else
    (CProg p, next_hop) : rst    

projectAuto :: AtomicProgram -> [AtomicProgram] -> Auto -> Auto
projectAuto trueAct actAlts auto =
  let delta' =
        Map.foldrWithKey (\state transitions ->
                            Map.insert state
                            (foldr (project_trans_list trueAct actAlts) [] transitions)
                         ) Map.empty (delta auto) in
  Auto { start = start auto
       , delta = delta'
       , final = final auto}
        
binary combine recFun left right = (recFun left) `combine` (recFun right)

compileView :: Map AtomicProgram [AtomicProgram] -> Query -> Query
compileView _ QEmpty = QEmpty
compileView _ QAll = QAll
compileView view (QIdent s) =
  case Map.lookup s view of
    Nothing -> QIdent s
    Just [] -> QIdent s
    Just alts ->
      foldr (QUnion . QIdent ) QEmpty alts
    
compileView view (QApply q q') =
  binary QApply (compileView view) q q'

compileView view (QConcat q q') =
  binary QConcat (compileView view) q q'

compileView view (QUnion q q') =
  binary QUnion (compileView view) q q'

compileView view (QComplement q) =
  QComplement $ compileView view q

compileView view (QStar q) =
  QStar $ compileView view q


lookupAction :: [Action] -> AtomicProgram -> Maybe Action
lookupAction [] _ = Nothing
lookupAction (a:as) p = if name a == p then Just a else lookupAction as p

lookupView :: [(Agent, Query -> Query)] -> Agent -> Maybe (Query -> Query)
lookupView [] _ = Nothing
lookupView ((a, v): vs) agent = if a == agent then Just v else lookupView vs agent

testFromAtom :: Atom -> Test
testFromAtom Empty = TTrue
testFromAtom (Pos v a) = TVar v `TAnd` testFromAtom a
testFromAtom (Neg v a) = TNeg (TVar v) `TAnd` testFromAtom a

katFromAtom :: Atom -> Kat
katFromAtom = KTest . testFromAtom

katFromAction :: Action -> Kat
katFromAction act = Set.foldr (\(pre, post) kat ->
                                 katFromAtom pre `KSeq`
                                 KVar (name act) `KSeq`
                                 katFromAtom post `KUnion` kat
                              ) End (relation act)

compileQuery :: Context -> Query -> QueryResult
compileQuery ctx QEmpty = QAuto $ construct End 
compileQuery ctx QAll = QAuto $ construct (KStar Nop)
compileQuery ctx (QIdent s) =
  case (lookupAction (actionsc ctx) s, lookupView (viewsc ctx) s)  of
    (Just a, Nothing) -> QAuto $ construct $ katFromAction a
    (Nothing, Just f) -> QRel f
    (Nothing, Nothing) -> error ("UseBeforeDef. Could not find name " ++ s)
    (Just _, Just _) -> error ("Multiple occurences of name " ++ s)
    
compileQuery ctx (QApply q q') =
  case (compileQuery ctx q) of
    (QAuto _) -> error "Type Error: Cannot Apply an Automaton as a function"
    (QRel f) -> compileQuery ctx $ f q'
    
compileQuery ctx (QConcat q q') =
  case (compileQuery ctx q, compileQuery ctx q') of
    (QAuto a, QAuto a') -> QAuto (a `concatAuto` a')
    (QRel f, QRel f') -> QRel (\x -> f x `QConcat` f' x)
    (QRel _, QAuto _) -> error "cannot concat a function and an automaton"
    (QAuto _, QRel _) -> error "cannot concat an automaton and a function"

      
compileQuery ctx (QUnion q q') =
  case (compileQuery ctx q, compileQuery ctx q') of
    (QAuto a, QAuto a') -> QAuto (a `unionAuto` a')
    (QRel f, QRel f') -> QRel (\x -> f x `QUnion` f' x)
    (_, _) -> error "Cannot union a function and an automaton"
    
-- compileQuery ctx (QIntersect q q') = -- intersection is syntactic sugar
--   compileQuery ctx $
--   QComplement $ QComplement q `QUnion` QComplement q'

compileQuery ctx (QComplement q) =
  case compileQuery ctx q of
    QAuto a -> QAuto $ complementAuto (alphabetc ctx) a
    QRel f -> QRel $ (\q -> QComplement $ f q)

-- compileQuery ctx (QSubtract q q') = compileQuery ctx $
--                                     q `QIntersect` QComplement q'
  
compileQuery ctx (QStar q) =
  case compileQuery ctx q of
    QAuto a -> QAuto $ iterateAuto a
    QRel f -> QRel (\x -> QStar $ f x)

 
compileDecls :: Declarations -> Context
compileDecls (Program alphabet asserts actions views queries) =
  let mapSnd f = map (\(a, x) -> (a, f x)) in
  Context { alphabetc = alphabet
          , actionsc = map (\(n, p) -> compile_action n alphabet asserts p) actions
          , viewsc = mapSnd (compileView) views
          }

runQueries :: Declarations -> [(QueryName, QueryResult)]
runQueries decls =
  let context = compileDecls decls in
    map (\(name, query) -> (name, compileQuery context query)) (queries decls)

qplus :: Query -> Query
qplus query = query `QConcat` QStar query

accShow :: Show a => String -> a -> String -> String
accShow sep x str = sep ++ show x ++ str

showQueryResults :: Declarations -> String
showQueryResults decls =
  let queries = runQueries decls in
    foldr (\(name,res) accStr ->
              case res of
                QRel _ -> name ++ " is a function, so we cannot print it"
                QAuto a ->
                  let guardedStrings = foldr (accShow "\n\t") "\n" $
                                       nub $
                                       toLoopFreeStrings (alphabet decls) a  in
                  name ++ " identifies the following (loop-free) strings:" ++ guardedStrings ++  "-----\n\n" ++ accStr
          ) "" queries
