||| The lambductive core calculus
module Lambductive.Core

%default total

||| Terms of the language
public
data Term : Type where
  ||| Tarski-style universe
  U : Term
