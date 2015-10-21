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
containsAxiom (U level) = No universeNotContainsAxiom
  where
    universeNotContainsAxiom : Not (ContainsAxiom (U level))
    universeNotContainsAxiom ContainsAxiomAxiom impossible
