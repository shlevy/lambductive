||| Lambductive core calculus
module Lambductive.Core

%default total

||| Terms of the calculus
data Term : Type where
  ||| A type universe
  U : (level : Nat) -> Term
