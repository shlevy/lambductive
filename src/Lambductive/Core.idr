||| The lambductive core calculus
module Lambductive.Core

%default total

||| Terms of the language
public
data Term : Type where
  ||| Tarski-style universe
  |||
  ||| The level is marked for erasure because as long as a term typechecks
  ||| we don't care about what universe we're talking about
  ||| @ level The universe's level.
  U : .(level : Nat) -> Term

||| A proof of the well-formedness of the term
public
data WellFormed : Term -> Type where
  ||| Universes are well-formed types
  UType : WellFormed (U level)
