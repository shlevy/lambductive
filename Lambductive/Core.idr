||| Lambductive core calculus
module Lambductive.Core

%default total

data Term : Type where
  U : (level : Nat) -> Term
