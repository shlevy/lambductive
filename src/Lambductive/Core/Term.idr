||| Terms of the calculus
module Lambductive.Core.Term

%default total

||| Terms of the language
public
data Term : Type where
  ||| Tarski-style universe
  ||| @ level The universe's level
  U : (level : Nat) -> Term
  ||| Type code for universe
  ||| @ level The universe's level
  UCode : (level : Nat) -> Term
  ||| Lifting operator for type codes
  ||| @ level The level from which to lift a code
  ||| @ code The code to lift
  LiftCode : (level : Nat) -> (code : Term) -> Term
  ||| Interpretation operator for type codes
  ||| @ level The level whose codes we're interpreting
  ||| @ code The code to interpret
  InterpretCode : (level : Nat) -> (code : Term) -> Term
