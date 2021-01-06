{
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
  
module Parser where

import Lexer
import Syntax

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.Except

}

-- entry point
%name decls

-- entry point
%name decls 


-- Lexer structure
%tokentype { Token }

-- Token Names
%token
   assert  { TAssert }
   action  { TAction }
   agent   { TAgent }
   world   { TWorld }
   query   { TQuery }
   macro   { TMacro }
   test    { TTest }
   IDENT   { TId $$ }
   COMMENT { TComment $$ }
   '='     { TEq }
   '('     { TLParen }
   ')'     { TRParen }
   '{'     { TLBracket }
   '}'     { TRBracket }
   '0'     { TZero }
   '1'     { TOne  }
   '+'     { TUnion }
   ';'     { TSeq }
   '~'     { TTilde }
   '_'     { TUnderscore }
   '*'     { TStar }
   '->'    { TArrow } 
   '&'     { TAmper}

-- Operator Associativity and Precedence
%left ';'
%left '&'
%left '+'
%left '~'
%right '*'
%%


Declarations : Declaration                { $1 }
             | Declaration Declarations   { combineDecls $1 $2 }

-- Programs form a semigroup
Declaration : Alphabet                    { Program $1        [] [] [] []   Map.empty}
            | Assertion                   { Program Set.empty $1 [] [] []   Map.empty}
            | Action                      { Program Set.empty [] $1 [] []   Map.empty}
            | View                        { Program Set.empty [] [] $1 []   Map.empty}
            | Query                       { Program Set.empty [] [] [] [$1] Map.empty}
            | Macro                       { Program Set.empty [] [] [] []   $1}
            | '{' Declaration '}'         { $2 }


-- Alphabet
Alphabet :  world '=' Worlds            { Set.fromList $3 }
 
Worlds : IDENT                          { [AtomicTest $1]  }
       | IDENT '+' Worlds               { AtomicTest $1 : $3 }

 
-- Assertions

Assertion : assert Test                 { [ $2 ] }

Test : '0'                              { TFalse }
     | '1'                              { TTrue }
     | Test '&' Test                    { TAnd $1 $3 }
     | Test '+' Test                    { TOr $1 $3 }
     | IDENT                            { TVar (AtomicTest $1) }
     | '~' Test                         { TNeg $2 }
     | '(' Test ')'                     { $2 }


-- Actions
Action : action IDENT '=' Kat           { [(AtomicProgram $2, $4)] }


Kat : '0'                               { kzero } 
    | '1'                               { kepsilon }
    | IDENT                             { kvar (AtomicProgram $1) }
    | test Test                         { ktest $2 }
    | Kat ';' Kat                       { kseq $1 $3 }
    | Kat '+' Kat                       { kunion $1 $3 }
    | Kat '*'                           { kstar $1 }
    | '(' Kat ')'                       { $2 }


-- Views / Alternative Relations
View : agent IDENT '=' Alts             { [($2, Map.fromList $4)] } 

Alts : '(' IDENT '->' AltList ')'       { [(AtomicProgram $2, $4)] }
     | '(' IDENT '->' AltList ')' Alts  { (AtomicProgram $2, $4) : $6 }

AltList : IDENT                         { [AtomicProgram $1] }
        | IDENT '+' AltList             { AtomicProgram $1 : $3 }


-- queries
Query : query IDENT '=' QueryKat        { ($2, "", $4) }
      | Comms query IDENT '=' QueryKat  { ($3, $1, $5) }

Comms : COMMENT                         { $1 }
      | COMMENT Comms                   { $1 ++ "\n" ++ $2 }

      
QueryKat : '0'                          { QEmpty }
         | '_'                          { QAll }
         | '1'                          { QEpsilon }
         | IDENT                        { QIdent $1 }
         | QueryKat '(' QueryKat ')'    { QApply $1 $3 }
         | QueryKat ';' QueryKat        { QConcat $1 $3 }
         | QueryKat '&' QueryKat        { QIntersect $1 $3 }
         | QueryKat '+' QueryKat        { QUnion $1 $3 }
         | '~' QueryKat                 { QComplement $2 }
         | QueryKat '*'                 { QStar $1 }
         | test Test                    { QTest $2 }
         | '(' QueryKat ')'             { $2 }


-- Test Macros
Macro : macro IDENT '=' Test            {Map.singleton (AtomicTest $2) $4}


{
happyError = undefined

commQuery :: String -> (String, Query) -> (String, Query)
commQuery s (s', q) = (s ++ "\n" ++ s' , q)

parse :: String -> Declarations
parse = decls . alexScanTokens

}
