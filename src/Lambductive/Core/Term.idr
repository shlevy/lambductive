||| Terms of the calculus
module Lambductive.Core.Term

%default total

||| Terms of the language
|||
||| For types that have type codes, the same term is used for both and context is used to disambiguate.
|||
||| The type code interpretation operator and lift operators are inferred from context.
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
  ||| Tarski-style universe type and type code
  ||| @ level The universe's level
  U : (level : Term) -> Term
