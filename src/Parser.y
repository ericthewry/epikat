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
   test    { TTest }
   IDENT   { TId $$ }
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
Declaration : Alphabet                    { Program $1        [] [] [] [] }
            | Assertion                   { Program Set.empty $1 [] [] [] }
            | Action                      { Program Set.empty [] $1 [] [] }
            | View                        { Program Set.empty [] [] $1 [] }
            | Query                       { Program Set.empty [] [] [] $1 }
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


Kat : '0'                               { KZero }
    | '1'                               { KEpsilon }
    | IDENT                             { KVar (AtomicProgram $1) }
    | test Test                         { KTest $2 }
    | Kat ';' Kat                       { KSeq $1 $3 }
    | Kat '+' Kat                       { KUnion $1 $3 }
    | Kat '*'                           { KStar $1 }
    | '(' Kat ')'                       { $2 }


-- Views / Alternative Relations
View : agent IDENT '=' Alts             { [($2, Map.fromList $4)] } 

Alts : '(' IDENT '->' AltList ')'       { [(AtomicProgram $2, $4)] }
     | '(' IDENT '->' AltList ')' Alts  { (AtomicProgram $2, $4) : $6 }

AltList : IDENT                         { [AtomicProgram $1] }
        | IDENT '+' AltList             { AtomicProgram $1 : $3 }


-- queries
Query : query IDENT '=' QueryKat        { [($2, $4)] }

QueryKat : '0'                          { QEmpty }
         | '_'                          { QAll }
         | '1'                          { QEpsilon }
         | IDENT                        { QIdent $1 }
         | test Test                    { QTest $2 }
         | QueryKat '(' QueryKat ')'    { QApply $1 $3 }
         | QueryKat ';' QueryKat        { QConcat $1 $3 }
         | QueryKat '&' QueryKat        { QIntersect $1 $3 }
         | QueryKat '+' QueryKat        { QUnion $1 $3 }
         | '~' QueryKat                 { QComplement $2 }
         | QueryKat '*'                 { QStar $1 }
         | '(' QueryKat ')'             { $2 }

{
happyError = undefined

parse :: String -> Declarations
parse = decls . alexScanTokens

}
