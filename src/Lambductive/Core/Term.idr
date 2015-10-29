||| Terms of the calculus
module Lambductive.Core.Term

import Pruviloj.Derive.DecEq

%default total

||| Terms of the language
|||
||| Universes are (strongly) à la Tarski.
|||
||| There is no term for any kind of "base" level. Instead, all terms referencing universes must be made level polymorphic by taking the level as a function argument.
public
data Term : Type where
  ||| The type of universe levels
  Level : Term
  ||| The successor of a level
  |||
  ||| The successor of a level is the level of the universe which contains this level's universe's type code.
  ||| @ level The level whose successor we're constructing
  SuccLevel : (level : Term) -> Term
  ||| A universe of type codes
  ||| @ level The universe's level
  U : (level : Term) -> Term
  ||| The type code of a universe
  ||| @ level The universe's level
  UCode : (level : Term) -> Term
  ||| Interpret a type code
  ||| @ level The level of the code's universe
  ||| @ code The code to interpret
  InterpretCode : (level : Term) -> (code : Term) -> Term
  ||| Lift a type code to the successor universe
  ||| @ level The level of the universe we're lifting from
  ||| @ code The code we're lifting to the new universe
  LiftCode : (level : Term) -> (code : Term) -> Term

decTermEq : (term1, term2 : Term) -> Dec (term1 = term2)
%runElab (deriveDecEq `{decTermEq})

instance DecEq Term where
  decEq = decTermEq
