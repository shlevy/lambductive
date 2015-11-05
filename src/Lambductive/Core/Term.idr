||| Terms of the calculus
module Lambductive.Core.Term

import Pruviloj.Derive.DecEq

%default total

||| Terms of the language
|||
||| There is no term for any kind of "base" universe level. Instead, all terms referencing universes must be made level polymorphic by taking the level as a function argument.
public
data Term : Type where
  ||| The type of universe levels
  Level : Term
  ||| The successor of a level
  |||
  ||| The successor of a level is the level of the universe which contains this level's universe.
  ||| @ level The level whose successor we're constructing
  SuccLevel : (level : Term) -> Term
  ||| A universe of types
  ||| @ level The universe's level
  U : (level : Term) -> Term
  ||| A dependent function type
  ||| @ domain The domain of the function
  ||| @ range The (possibly dependent) range of the function
  Pi : (domain : Term) -> (range : Term) -> Term

decTermEq : (term1, term2 : Term) -> Dec (term1 = term2)
%runElab (deriveDecEq `{decTermEq})

instance DecEq Term where
  decEq = decTermEq
