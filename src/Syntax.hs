module Syntax where

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set
 
data AtomicProgram = AtomicProgram String deriving (Eq, Ord)
data AtomicTest = AtomicTest String deriving (Eq, Ord)

instance Show AtomicProgram where
  show (AtomicProgram s) = s

instance Show AtomicTest where
  show (AtomicTest s) = s

data Kat =
  KZ -- End :: Kat
  | KEps -- Nop :: Kat
  | KBool Test -- KTest :: Test -> Kat
  | KEvent AtomicProgram -- KVar :: AtomicProgram -> Kat
  | KSequence Kat Kat       -- KSeq :: Kat -> Kat -> Kat  
  | KPlus Kat Kat     -- KUnion :: Kat -> Kat -> Kat
  | KAnd Kat Kat 
  | KIter Kat          -- KStar :: Kat -> Kat
  deriving (Eq, Ord)

instance Show Kat where
  show KZ = "0"
  show KEps = "1"
  show (KBool t) = "(" ++ show t ++ ")"
  show (KEvent s) = show s
  show (KSequence p q) = show p ++ ";" ++ show q
  show (KPlus p q) = "(" ++ show p ++ " + " ++ show q ++ ")"
  show (KAnd p q) = "(" ++ show p ++ " & " ++ show q ++ ")"
  show (KIter p) = "(" ++ show p ++ ")*"

kzero = KZ
kepsilon = KEps
kone = kepsilon
kvar = KEvent

kseq KEps k' = k'
kseq k KEps = k
kseq KZ _ = KZ
kseq _ KZ = KZ
kseq (KBool t) (KBool t') = ktest (t `TAnd` t')
kseq k k' = KSequence k k'

kunion KZ k' = k'
kunion k KZ = k
kunion (KBool t) (KBool t') = ktest (t `TOr` t')
kunion k k' = KPlus k k'

kstar (KEps) = kepsilon
kstar (KZ) = kzero
kstar (KIter k) = kstar k
kstar k = KIter k

ktest = KBool

kand KZ _ = KZ
kand _ KZ = KZ
kand k k' = KAnd k k'


data Test =
  TTrue
  | TFalse
  | TAnd Test Test
  | TOr Test Test
  | TVar AtomicTest
  | TNeg Test
  deriving (Eq,Ord)

instance Show Test where
  show TTrue = "1"
  show TFalse = "0"
  show (TAnd p q) = show p ++ "&" ++ show q
  show (TOr p q) = show p ++ " + " ++ show q
  show (TVar v) = show v
  show (TNeg x) = "~" ++ show x


ifElse :: Test -> Kat -> Kat -> Kat
ifElse cond tru fls = -- if (cond) { tru } else { fls } =^= cond ; tru + ~cond;fls
  (ktest cond `kseq` tru)
  `kunion` (ktest (TNeg cond) `kseq` fls)

data Query = -- a relational alegebra for Queries
  QEmpty -- Uninhabited
  | QEpsilon -- the empty string
  | QAll -- Inhabited by every one-character string
  | QIdent String -- An Agent, View, or Previously-defined Query
  | QTest Test  -- check a test
  | QApply Query Query -- QApply f x is f(x)
  -- | QDomain Query -- get domain of agent's view
  -- | QCodom Query -- get codomain of agents' view
  | QConcat Query Query -- concatenate the output of two queries
  | QUnion Query Query -- get the union of two queries
  | QIntersect Query Query  -- intersect two queries
  | QComplement Query -- Negate the query
  -- | QSubtract Query -- Remove an set from the query
  | QStar Query -- get the least upper bound of a relation 
  deriving (Eq, Ord)

instance Show Query  where
  show QEmpty = "0"
  show QEpsilon = "1"
  show QAll   = "_"
  show (QIdent s) = s
  show (QApply f x) = show f ++ "(" ++ show x ++ ")"
  -- show (QDomain q) = "dom(" ++ show q ++ ")"
  -- show (QCodom q) = "codom(" ++ show q ++ ")"
  show (QConcat q q') = show q ++  " ; " ++ show q'
  show (QUnion q q') = show q ++ " + " ++ show q'
  show (QIntersect q q') = show q ++ " & "  ++ show q'
  show (QComplement q) = "~" ++ show q
  -- show (QSubtract q q') = show q ++ " \\ " show q'
  show (QStar q) = "(" ++ show q ++ ")*"

type Agent = String
type QueryName = String
type NamedQuery = (QueryName, String, Query)
type QueryData = [NamedQuery]
type Macros = Map AtomicTest Test


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



data Declarations =
  Program { alphabet :: Set AtomicTest        -- the alphabet of world-states
          , assertions :: [Test] -- conditions that specify consistent worlds
          , actions :: [(AtomicProgram, Effect)] -- the world actions and their relations
          , views :: [(Agent, Map AtomicProgram [AtomicProgram])] -- alternative relations
          , queries :: QueryData -- queries expressed in KAT
          , macros :: Macros
          } deriving (Eq,Show)

combineDecls :: Declarations -> Declarations -> Declarations
combineDecls decl decl' =
  let join j f = f decl `j` f decl' in
  Program { alphabet= join Set.union alphabet
          , assertions = join (++) assertions
          , actions = join (++) actions
          , views = join  (++) views
          , queries = join (++) queries
          , macros = join Map.union macros}
