||| Proofs about the calculus
module Lambductive.Proof

import Lambductive.Core

%default total

||| A proof that a term contains an axiom
||| @ term The term that contains an axiom
data ContainsAxiom : (term : Term) -> Type where
  ||| An axiom contains an axiom
  ContainsAxiomAxiom : ContainsAxiom (Axiom name)

||| A decision procedure for `ContainsAxiom`
||| @ term The term we're checking for an axiom
containsAxiom : (term : Term) -> Dec (ContainsAxiom term)
containsAxiom (Axiom name) = Yes ContainsAxiomAxiom
containsAxiom (U level) = No universeNotContainsAxiom where
  universeNotContainsAxiom ContainsAxiomAxiom impossible

||| A decision procedure for validity
||| @ term The term we're deciding about
||| @ judgment The judgment we're deciding about
validJudgment : (term : Term) -> (judgment : Judgment) -> Dec (ValidJudgment term judgment)
validJudgment (Axiom name) judgment = Yes AxiomAny
validJudgment (U _) JudgmentType = Yes UType
validJudgment (U _) (JudgmentValue _) = No universeNotValue where
   universeNotValue UType impossible
