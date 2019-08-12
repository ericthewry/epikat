module Epik where


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

type Agent = String
type QueryName = String
type Param = String

data Declarations =
  Program { alphabet :: Set AtomicTest        -- the alphabet of world-states
          , actions :: [(AtomicProgram, Kat)] -- the world actions and their relations
          , views :: [(Agent, Map AtomicProgram [AtomicProgram])] -- alternative relations
          , queries :: [(QueryName, Query)] -- queries expressed in KAT
          } deriving (Eq,Show)

data Context =
  Context { alphabetc :: Set AtomicTest
          , actionsc :: [Action]
          , viewsc :: [(Agent, Auto -> Auto)]}
  
data Action = Action { name :: String
                     , relation :: Set (Atom, Atom)
                     } deriving (Eq, Show)

data QueryResult =
  QAuto Auto
  | QRel (Auto -> Auto)


gs_relation :: (Ord a, Ord b) =>
               (GuardedString -> a) ->
               (GuardedString -> b) ->
               Set GuardedString    -> Set (a,b)
gs_relation f g = Set.map (\s -> (f s, g s)) 

compile_action :: String -> Set AtomicTest -> Kat -> Action
compile_action name alphabet prog =
  Action { name = name
         , relation = gs_relation first last $ gs_interp alphabet prog
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
        

compile_views :: Set AtomicTest -> Map AtomicProgram [AtomicProgram] -> Auto -> Auto
compile_views alphabet view auto = Map.foldrWithKey projectAuto auto view


lookupAction :: [Action] -> AtomicProgram -> Maybe Action
lookupAction [] _ = Nothing
lookupAction (a:as) p = if name a == p then Just a else lookupAction as p

lookupView :: [(Agent, Auto -> Auto)] -> Agent -> Maybe (Auto -> Auto)
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
                                 katFromAtom post
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
  case (compileQuery ctx q, compileQuery ctx q') of
    (QAuto _, _) -> error "Type Error: Cannot Apply an Automaton as a function"
    (QRel f, QRel f') -> QRel (\x -> f' (f x)) 
    (QRel f, QAuto a) -> QAuto (f a)
    
compileQuery ctx (QConcat q q') =
  case (compileQuery ctx q, compileQuery ctx q') of
    (QAuto a, QAuto a') -> QAuto (a `concatAuto` a')
    (QRel f, QAuto a) -> QRel (\x -> f x `concatAuto` a)
    (QAuto a, QRel f) -> QRel (\x -> a `concatAuto` f x)
    (QRel f, QRel f') -> QRel (\x -> f x `concatAuto` f' x)
      
compileQuery ctx (QUnion q q') =
  case (compileQuery ctx q, compileQuery ctx q') of
    (QAuto a, QAuto a') -> QAuto (a `unionAuto` a')
    (QAuto a, QRel f) -> QRel (\x -> f x `unionAuto` a)
    (QRel f, QAuto a) -> QRel (\x -> f x `unionAuto` a)
    (QRel f, QRel f') -> QRel (\x -> f x `unionAuto` f' x)
    
-- compileQuery ctx (QIntersect q q') = -- intersection is syntactic sugar
--   compileQuery ctx $
--   QComplement $ QComplement q `QUnion` QComplement q'

compileQuery ctx (QComplement q) =
  case compileQuery ctx q of
    QAuto a -> QAuto $ complementAuto a
    QRel f -> QRel $ (\x -> complementAuto (f x))

-- compileQuery ctx (QSubtract q q') = compileQuery ctx $
--                                     q `QIntersect` QComplement q'
  
compileQuery ctx (QStar q) =
  case compileQuery ctx q of
    QAuto a -> QAuto $ iterateAuto a
    QRel f -> QRel (\x -> iterateAuto $ f x)

 
compileDecls :: Declarations -> Context
compileDecls decls =
  Context { alphabetc = alphabet decls
          , actionsc = map (\(n, p) -> compile_action n (alphabet decls) p) (actions decls)
          , viewsc = map (\(a, m) -> (a, compile_views (alphabet decls) m)) (views decls)
          }

runQueries :: Declarations -> [(QueryName, QueryResult)]
runQueries decls =
  let context = compileDecls decls in
    map (\(name, query) -> (name, compileQuery context query)) (queries decls)


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
                                       toLoopFreeStrings (alphabet decls) a  in
                  name ++ " identifies the following (loop-free) strings:" ++ guardedStrings ++  "\n\n" ++ accStr
          ) "" queries
