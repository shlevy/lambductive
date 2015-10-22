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
containsAxiom (Axiom _) = Yes ContainsAxiomAxiom
containsAxiom (U _) = No universeNotContainsAxiom where
  universeNotContainsAxiom ContainsAxiomAxiom impossible
containsAxiom (UCode _) = No universeCodeNotContainsAxiom where
  universeCodeNotContainsAxiom ContainsAxiomAxiom impossible

||| A decision procedure for validity
||| @ term The term we're deciding about
||| @ judgment The judgment we're deciding about
validJudgment : (term : Term) -> (judgment : Judgment) -> Dec (ValidJudgment term judgment)
validJudgment (Axiom _) judgment = Yes AxiomAny
validJudgment (U _) JudgmentType = Yes UType
validJudgment (U _) (JudgmentValue _) = No universeNotValue where
  universeNotValue UType impossible
validJudgment (UCode _) JudgmentType = No universeCodeNotType where
  universeCodeNotType UType impossible
validJudgment (UCode _) (JudgmentValue (Axiom _)) = No universeCodeNotAxiom where
  universeCodeNotAxiom AxiomAny impossible
validJudgment (UCode _) (JudgmentValue (UCode _)) = No universeCodeNotUniverseCode where
  universeCodeNotUniverseCode UCodeU impossible
validJudgment (UCode level1) (JudgmentValue (U level2)) with (decEq (S level1) level2)
  validJudgment (UCode level1) (JudgmentValue (U _)) | Yes Refl = Yes UCodeU
  | No p = No (universeCodeNotInNotSuccUniverse level1 level2 p) where
    universeCodeNotInNotSuccUniverse _ _ p (UCodeU) = p Refl
