module Syntax where

type AtomicProgram = String
type AtomicTest = String

data Kat =
  End -- End :: Kat
  | Nop -- Nop :: Kat
  | KTest Test -- KTest :: Test -> Kat
  | KVar AtomicProgram -- KVar :: AtomicProgram -> Kat
  | KSeq Kat Kat       -- KSeq :: Kat -> Kat -> Kat  
  | KUnion Kat Kat     -- KUnion :: Kat -> Kat -> Kat
  | KStar Kat          -- KStar :: Kat -> Kat
  deriving (Eq)

instance Show Kat where
  show End = "0"
  show Nop = "1"
  show (KTest t) = show t
  show (KSeq p q) = show p ++ ";" ++ show q
  show (KUnion p q) = show p ++ " + " ++ show q
  show (KStar p) = "(" ++ show p ++ ")*"
  show (KVar s) = s

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
  show (TAnd p q) = show p ++ ";" ++ show q
  show (TOr p q) = show p ++ " || " ++ show q
  show (TVar v) = v
  show (TNeg x) = "~" ++ show x


ifElse :: Test -> Kat -> Kat -> Kat
ifElse cond tru fls = -- if (cond) { tru } else { fls } =^= cond ; tru + ~cond;fls
  (KTest cond `KSeq` tru)
  `KUnion` (KTest (TNeg cond) `KSeq` fls)

data Query = -- a relational alegebra for Queries
  QEmpty -- Uninhabited
  | QAll -- Inhabited by every string
  | QIdent String -- An Agent, View, or Parameter
  | QApply Query Query -- QApply f x is f(x)
  -- | QDomain Query -- get domain of agent's view
  -- | QCodom Query -- get codomain of agents' view
  | QConcat Query Query -- concatenate the output of two queries
  | QUnion Query Query -- get the union of two queries
  -- | QIntersect Query Query  -- intersect two queries
  | QComplement Query -- Negate the query
  -- | QSubtract Query -- Remove an set from the query
  | QStar Query -- get the least upper bound of a relation 
  deriving Eq

instance Show Query  where
  show QEmpty = "0"
  show QAll   = "1"
  show (QIdent s) = s
  show (QApply f x) = show f ++ "(" ++ show x ++ ")"
  -- show (QDomain q) = "dom(" ++ show q ++ ")"
  -- show (QCodom q) = "codom(" ++ show q ++ ")"
  show (QConcat q q') = show q ++  " ^ " ++ show q'
  show (QUnion q q') = show q ++ " + " ++ show q'
  -- show (QIntersect q q') = show q ++ " & "  ++ show q'
  show (QComplement q) = "~" ++ show q
  -- show (QSubtract q q') = show q ++ " \\ " show q'
  show (QStar q) = "(" ++ show q ++ ")*"
