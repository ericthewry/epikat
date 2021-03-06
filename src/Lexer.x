{
{-# LANGUAGE FlexibleContexts #-}

module Lexer where

import Prelude

import Control.Monad.Except

}

%wrapper "basic"

$loweralpha = [a-z]
$upperalpha = [A-Z]
$alpha = [$loweralpha $upperalpha]
$digit = [0-9]
$ident = [$alpha $digit \_ \']


tokens :-
  $white +         ;
  "#".*            ;
  "--".*           { \s -> TComment s }
  restrict         { \s -> TAssert }
  event            { \s -> TAction }
  agent            { \s -> TAgent }
  state            { \s -> TWorld }
  query            { \s -> TQuery }
  macro            { \s -> TMacro }
  test             { \s -> TTest }
  [=]              { \s -> TEq }
  \-\>             { \s -> TArrow }
  \(               { \s -> TLParen }
  \)               { \s -> TRParen }
  \{               { \s -> TLBracket }
  \}               { \s -> TRBracket }
  0                { \s -> TZero }
  1                { \s -> TOne }
  $alpha ($ident)* { \s -> TId s }
  [\+]             { \s -> TUnion }
  [\;]             { \s -> TSeq }
  [\*]             { \s -> TStar }
  [\~]             { \s -> TTilde }
  [\&]             { \s -> TAmper }
  [\_]             { \s -> TUnderscore }
  [\:]             { \s -> TPair }

{

data Token =
     TZero
     | TOne
     | TId String
     | TComment String
     | TTest
     | TUnion
     | TSeq
     | TTilde
     | TUnderscore
     | TAmper
     | TStar
     | TLParen
     | TRParen
     | TLBracket
     | TRBracket
     | TArrow
     | TQuery
     | TMacro
     | TAssert
     | TEq
     | TWorld
     | TAction
     | TAgent
     | TPair
     deriving(Eq, Show)

scanTokens :: String -> Except String [Token]
scanTokens str = go ('\n',[],str) where 
  go inp@(_,_bs,str) =
    case alexScan inp 0 of
     AlexEOF -> return []
     AlexError _ -> throwError "Invalid lexeme."
     AlexSkip  inp' len     -> go inp'
     AlexToken inp' len act -> do
      res <- go inp'
      let rest = act (take len str)
      return (rest : res)

}
