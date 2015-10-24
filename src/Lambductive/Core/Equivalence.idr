||| Equivalences between terms
module Lambductive.Core.Equivalence

import Lambductive.Core.Term

%default total

||| An equivalence between terms
||| @ lhs The left hand side of the equivalence
||| @ rhs The right hand side of the equivalence
public
data Equivalence : (lhs : Term) -> (rhs : Term) -> Type where
  ||| The interpretation of the universe code is the universe
  InterpretUCodeIsU : Equivalence (InterpretCode (S level) (UCode level)) (U level)
  ||| Equivalence is a congruence over LiftCode
  ||| @ equivalence : The equivalence we're lifting into LiftCode
  LiftCodeCongruence : (equivalence : Equivalence lhs rhs) -> Equivalence (LiftCode level lhs) (LiftCode level rhs)
