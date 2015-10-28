||| Proofs about the calculus
module Lambductive.Proof

import Lambductive.Core.Term
import Lambductive.Core.Equivalence
import Lambductive.Core.Judgment

%default total

-- Until we have pi types, we can't inhabit any types because there's no base level
instance Uninhabited (Judgment _ (SortValue _)) where
  uninhabited (SuccLevelLevel judgment) = uninhabited judgment
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

||| A structured proof that a given term cannot be judged to have a given sort
||| @ term The term we're judging
||| @ sort The sort that cannot be assigned
public
data BadJudgment : (term : Term) -> (sort : Sort) -> Type where
  ||| There are no values (until we have pi types)
  NoValues : BadJudgment term (SortValue type)
  ||| If a universe's argument is not a level, the universe is not a type
  ||| @ levelNotLevel Proof that `level` is not a level
  UArgumentNotLevel : (levelNotLevel : BadJudgment level (SortValue Level)) -> BadJudgment (U level) SortType
  ||| The successor of a level is not a type
  SuccLevelNotType : BadJudgment (SuccLevel level) SortType

||| If we have a bad judgment of a given term and sort pair, there is no valid judgment of that term having that sort
||| @ badJudgment The proof that `term` cannot be assigned `sort`
public
badJudgmentNotJudgment : (badJudgment : BadJudgment term sort) -> Not (Judgment term sort)
badJudgmentNotJudgment NoValues judgment = uninhabited judgment
badJudgmentNotJudgment (UArgumentNotLevel notLevel) (UType levelLevel) = badJudgmentNotJudgment notLevel levelLevel
badJudgmentNotJudgment (UArgumentNotLevel notLevel) (InterpretCodeType codeJudgment) = badJudgmentNotJudgment notLevel (getLevel codeJudgment) where
  getLevel : Judgment (U level) (SortValue (U _)) -> Judgment level (SortValue Level)
  getLevel (UCodeU levelLevel) = levelLevel
  getLevel (LiftCodeU code) = getLevel code
badJudgmentNotJudgment SuccLevelNotType (InterpretCodeType (LiftCodeU succLevelU)) = succLevelNotU succLevelU where
  succLevelNotU : Judgment (SuccLevel _) (SortValue (U _)) -> Void
  succLevelNotU (LiftCodeU succLevelU) = succLevelNotU succLevelU

||| A decision about whether a term can be assigned a sort
||| @ term The term we're deciding about
||| @ sort The sort we're deciding applies to `term` or not
public
data JudgmentDecision : (term : Term) -> (sort : Sort) -> Type where
  ||| The term can be assigned the sort
  ||| @ judgment The judgment assigning `term` the sort `sort`
  Good : (judgment : Judgment term sort) -> JudgmentDecision term sort
  ||| The term cannot be assigned the sort
  ||| @ badJudgment The proof that `term` cannot be assigned the sort `sort`
  Bad : (badJudgment : BadJudgment term sort) -> JudgmentDecision term sort

||| A decision procedure for sort judgment
||| @ term The term we're deciding about
||| @ sort The sort we're deciding applies to `term` or not
public
judgmentDecidable : (term : Term) -> (sort : Sort) -> JudgmentDecision term sort
judgmentDecidable _ (SortValue _) = Bad NoValues
judgmentDecidable Level SortType = Good LevelType
judgmentDecidable (U level) SortType with (judgmentDecidable level (SortValue Level))
  | Good judgment = Good (UType judgment)
  | Bad notLevel = Bad (UArgumentNotLevel notLevel)
judgmentDecidable (SuccLevel level) SortType = Bad SuccLevelNotType
