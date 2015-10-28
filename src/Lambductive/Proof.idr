||| Proofs about the calculus
module Lambductive.Proof

import Lambductive.Core.Term
import Lambductive.Core.Equivalence
import Lambductive.Core.Judgment

%default total

-- Until we have pi types, we can't inhabit any types because there's no base level
instance Uninhabited (Judgment _ (SortValue _)) where
  uninhabited (SuccLevel judgment) = uninhabited judgment
  uninhabited (UCodeU judgment) = uninhabited judgment
  uninhabited (LiftCodeU judgment) = uninhabited judgment

||| The type of a value is of sort `type`
||| @ value The value whose type's sort we're judging
public
valueTypeType : (value : Judgment _ (SortValue type)) -> Judgment type SortType
valueTypeType = absurd

||| Transport a judgment along an equivalence
||| @ equivalence The equivalence we're transporting along
||| @ judgment The judgment we're transporting
public
transportJudgment : (equivalence : Equivalence term1 term2) -> (judgment : Judgment term1 sort) -> Judgment term2 sort
%runElab (defineFunction $ DefineFun `{transportJudgment} [])

||| A decision procedure for sort judgment
||| @ term The term we're deciding about
||| @ sort The sort we're deciding applies to `term` or not
public
judgmentDecidable : (term : Term) -> (sort : Sort) -> Dec (Judgment term sort)
judgmentDecidable Level SortType = Yes LevelType
judgmentDecidable (U level) SortType = No levelUninhabited where
  levelUninhabited (UType levelJudgment) = absurd levelJudgment
  levelUninhabited (InterpretCodeType codeU) = absurd codeU
judgmentDecidable (SuccLevel level) SortType = No succLevelNotType where
  succLevelNotType LevelType impossible
  succLevelNotType (UType _) impossible
  succLevelNotType (InterpretCodeType codeU) = absurd codeU
judgmentDecidable _ (SortValue _) = No absurd
