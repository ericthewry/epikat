module FstGen where
-- To test it
--  ghc -o SyntaxA SyntaxA.hs
--  ./SyntaxA > m1.fst

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Syntax
import Epik
import GuardedStrings

-- Effect formulas as in Figure 1.
data Effect =
  EPair Test Test
  | EOr Effect Effect
  | EAnd Effect Effect
  | ENeg Effect
  deriving (Eq,Ord)

-- This is not used in generating Fst.
instance Show Effect where
  show (EPair u v) = show u ++ " : " ++ show v
  show (EOr u v) = show u ++ " + " ++ show v
  show (EAnd u v) = show u ++ " & " ++ show v
  show (ENeg x) = "~" ++ show x

-- combineDecls decl decl' =
--  let join j f = f decl `j` f decl' in
--  Program { alphabet= join (Set.union) alphabet
--          , assertions = join (++) assertions
--          , events = join (++) events
--         , agents = join  (++) agents

-- Construct the alphabet
-- tests ["h","t","h"] ~> fromList [h,t] :: Set AtomicTest
tests :: [String] -> Set AtomicTest
tests [] = Set.empty
tests (a : as) = Set.insert (AtomicTest a) (tests as)


-- Construct effect formulas for tests remaining constant etc.

constantEffect :: AtomicTest -> Effect
constantEffect a = EOr (EPair (TVar a) (TVar a)) (EPair (TNeg (TVar a)) (TNeg (TVar a)))
-- constantEffect (AtomicTest "h")  -> h : h + ~h : ~h

-- Precondition that fluent a is true
-- preTrue (AtomicTest "h") ~> h : 1
preTrue :: AtomicTest -> Effect
preTrue a = EPair (TVar a) TTrue


-- Precondition that fluent a is false
preFalse :: AtomicTest -> Effect
preFalse a = EPair (TNeg (TVar a)) TTrue

-- All the fluents in the set are constant.
-- constantEffects (tests ["c1","c2","c3"])  ~> c1 : c1 + ~c1 : ~c1 & c2 : c2 + ~c2 : ~c2 & c3 : c3 + ~c3 : ~c3
constantEffects :: (Set AtomicTest) -> Effect
constantEffects as = let bs = (Set.toList as)
  in (constantEffects0 bs)
   where constantEffects0 [x] = constantEffect x
         constantEffects0 (x : xs) = EAnd (constantEffect x) (constantEffects0 xs)
         constantEffects0 [] = EPair TTrue TTrue

-- Construct a list of Fst declarations that define
--  Bool
--  St0 primitive atoms
--  each fluent in set the set as
--  St atoms restricted by state formula phi
testDef :: (Set AtomicTest) -> Test -> [String]
testDef as phi = ["define Bool [\"0\" | \"1\"];",                    -- Bool
                     "define St0 Bool^" ++ (show (length as)) ++ ";",   -- St0
                     "define St St0;"]                                  -- temporary St
                 ++ (testDef2 (Set.toList as))                       -- fluents
                 ++ ["define St St0 & " ++ (testFst phi) ++ ";"]        -- St
                 ++ [(unequalStPair as)]
  where testDef0 :: [AtomicTest] -> AtomicTest -> String
        testDef0 [y] x = (if (x == y) then "1" else "Bool")
        testDef0 (y : xs) x = (if (x == y) then "1" else "Bool") ++ " " ++ (testDef0 xs x)
        testDef1 :: [AtomicTest] -> AtomicTest -> String
        testDef1 ys x = "define " ++ (show x) ++ " [" ++ (testDef0 ys x) ++ "];"
        testDef2 :: [AtomicTest] -> [String]
        testDef2 ys = map (testDef1 ys) ys

-- Example
-- testDef (tests ["c1","c2","c3"])

-- Map a state formula to Fst syntax in a context where St and the fluents are defined.
testFst :: Test -> String 
testFst (TVar a) = (show a)
testFst TFalse = "[St - St]"
testFst TTrue = "St"
testFst (TOr x y) = "[" ++ (testFst x) ++ " | " ++ (testFst y) ++ "]"
testFst (TAnd x y) = "[" ++ (testFst x) ++ " & " ++ (testFst y) ++ "]"
testFst (TNeg x) = "[St - " ++ (testFst x) ++ "]"

-- For examples
-- testFst phi0 ~> "[[h | t] & [St - [h & t]]]"
-- testDef b0 phi0 ~>
phi0 = (TAnd (TOr (TVar (AtomicTest "h")) (TVar (AtomicTest "t"))) (TNeg (TAnd (TVar (AtomicTest "h")) (TVar (AtomicTest "t")))))
b0 = (tests ["h","t"])



-- Fst string with the form of a pair of non-matching atoms.
-- unequalStPair b0 ~> "define UnequalStPair [h [St - h]] | [[St - h] h] | [t [St - t]] | [[St - t] t];"
unequalStPair :: (Set AtomicTest) -> String
unequalStPair xs = "define UnequalStPair " ++ (disjoin (map unequalStPair0 (Set.toList xs))) ++ ";"
  where disjoin [x] = x
        disjoin (x : xs) = x ++ " | " ++ (disjoin xs)

unequalStPair0 :: AtomicTest -> String
unequalStPair0 x = "[" ++ (testFst x') ++ " " ++ (testFst (TNeg x')) ++ "] | [" ++
             (testFst (TNeg x')) ++ " " ++ (testFst x') ++ "]"
  where x' = (TVar x)
  



-- Definitions of event types from their effect formulas.
-- Define Event as the disjunction of the event types.

effectDef :: [(AtomicProgram, Effect)] -> [String]
effectDef xs = (map effectDef1 xs) ++ ["define Event " ++ (disjoin (map fst xs)) ++ ";"]
  where disjoin [x] = (show x)
        disjoin (x : xs) = (show x) ++ " | " ++ (disjoin xs)
 

effectDef1 :: (AtomicProgram, Effect) -> String
effectDef1 (e, eta) = "define " ++ (show e) ++ " " ++ (effectDef0 eta) ++ " & [St " ++ (show e) ++ " St];"
  where effectDef0 :: Effect -> String
        effectDef0 (EPair u v) = "[" ++ (testFst u) ++ " ? " ++ (testFst v) ++ "]"
        effectDef0 (EOr x y) = "[" ++ (effectDef0 x) ++ " | " ++ (effectDef0 y) ++ "]"
        effectDef0 (EAnd x y) = "[" ++ (effectDef0 x) ++ " & " ++ (effectDef0 y) ++ "]"
        effectDef0 (ENeg x) = "[[St ? St] - " ++ (effectDef0 x) ++ "]"


-- example
eta_a1 =  EAnd (preTrue (AtomicTest "h")) (constantEffects (tests ["h","t"]))
-- example
evspec :: [(AtomicProgram, Effect)]
evspec = [((AtomicProgram "a1"), EAnd (preTrue (AtomicTest "h")) (constantEffects (tests ["h","t"]))),
          ((AtomicProgram "a0"), EAnd (preFalse (AtomicTest "h")) (constantEffects (tests ["h","t"]))),
          ((AtomicProgram "b1"), EAnd (preTrue (AtomicTest "h")) (constantEffects (tests ["h","t"]))),
          ((AtomicProgram "b0"), EAnd (preFalse (AtomicTest "h")) (constantEffects (tests ["h","t"])))]

-- Definitions of agent epistemic alterntive relations.
-- Kat.fst defines KAT operations such as RelKst in Fst.



-- (Agent, [(AtomicProgram, [AtomicProgram])])

-- SIngle pair
eventRel0 :: (AtomicProgram,[AtomicProgram]) -> String
eventRel0 (e,es) = "[" ++ (show e) ++ " .x. [" ++ (disjoin es) ++ "]]"
  where disjoin [x] = (show x)
        disjoin (x : xs) = (show x) ++ " | " ++ (disjoin xs)

-- list of pairs
eventRel1 :: [(AtomicProgram,[AtomicProgram])] -> String
eventRel1 xs = "[" ++ (disjoin (map eventRel0 xs)) ++ "]"
  where disjoin [x] = x
        disjoin (x : xs) = x ++ " | " ++ (disjoin xs)

-- effect ((AtomicProgram "a1"), eta_a1)

amyspec = [(AtomicProgram "a1", map AtomicProgram ["a1"]),
           (AtomicProgram "a0", map AtomicProgram ["a0"]),
           (AtomicProgram "b1", map AtomicProgram ["b1","b0"]),
           (AtomicProgram "b0", map AtomicProgram ["b1","b0"])]

bobspec = [(AtomicProgram "b1", map AtomicProgram ["b1"]),
           (AtomicProgram "b0", map AtomicProgram ["b0"]),
           (AtomicProgram "a1", map AtomicProgram ["a1","a0"]),
           (AtomicProgram "a0", map AtomicProgram ["a1","a0"])]

agentspec = [("amy",amyspec),("bob",bobspec)]

agentDef :: [(Agent, [(AtomicProgram, [AtomicProgram])])] -> [String]
agentDef xs = ["source kat.fst;"] ++ (map agentDef0 xs)

agentDef0 :: (Agent, [(AtomicProgram, [AtomicProgram])]) -> String
agentDef0 (a,xs) = "define " ++ a ++ " RelKst(" ++ (eventRel1 xs) ++ ");"


-- I'm not sure this is doing the right thing In math we're aggregating
-- \/ (fst gs, last gs)
-- for every guarded string denoted by k The code above might be
-- making a different assumption about the structure of EAbstr but idk.
effectOfProgram :: Context -> Kat -> Effect
effectOfProgram ctx k =
  let strings = gs_interp 100 (atomsc ctx) k in
  foldr effectOfGSAcc (EPair TFalse TFalse) strings
  where effectOfGSAcc :: GuardedString -> Effect -> Effect
        effectOfGSAcc gs acc =
          EOr acc $
          EPair (testOfAtom $ first gs)
                (testOfAtom $ GuardedStrings.last gs)


events :: Context -> [(AtomicProgram, Effect)]
events ctx =
  let acts = actionsc ctx in
  map (\ a -> (name a, effectOfProgram ctx $ program a)) acts

agents :: Context -> [(Agent, [(AtomicProgram, [AtomicProgram])])]
agents ctx =
  let tolist (a,m) = (a, Map.toList m) in
  map tolist $ viewsc ctx

-- ModelSpecification -> String
fst_string :: Context -> String
fst_string ctx =
  unlines (testDef (alphabetc ctx) (assertion ctx)) ++ "\n" ++
  unlines (effectDef $ events ctx) ++ "\n" ++
  unlines (agentDef $ agents ctx)

gen_fst :: Declarations -> String
gen_fst = fst_string . compileDecls
