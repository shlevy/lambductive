||| Proofs about the calculus
module Lambductive.Proof

import Lambductive.Core.Term
import Lambductive.Core.Equivalence
import Lambductive.Core.Judgment

%default total

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
  ||| `Level` is not a value
  LevelNotValue : BadJudgment Level (SortValue type)

  ||| The successor of a level is not a type
  SuccLevelNotType : BadJudgment (SuccLevel level) SortType
  ||| The successor of a level is not a type code
  SuccLevelNotU : BadJudgment (SuccLevel level1) (SortValue (U level2))
  ||| The successor level of a term that is not a level is not a level
  ||| @ levelNotLevel Proof that `level` is not a level
  SuccLevelArgumentNotLevel : (levelNotLevel : BadJudgment level (SortValue Level)) -> BadJudgment (SuccLevel level) (SortValue Level)

  ||| If a universe's argument is not a level, the universe is not assignable any sort
  ||| @ levelNotLevel Proof that `level` is not a level
  UArgumentNotLevel : (levelNotLevel : BadJudgment level (SortValue Level)) -> BadJudgment (U level) sort
  ||| A universe is not a level
  UNotLevel : BadJudgment (U level) (SortValue Level)

  ||| If a value's proposed type is not a type, the value does not have that type
  TypeNotType : (typeNotType : BadJudgment type SortType) -> BadJudgment value (SortValue type)

instance Uninhabited (Judgment (SuccLevel _) (SortValue (U _))) where
  uninhabited (LiftCodeU succLevelU) = uninhabited succLevelU

getUCodeLevel : Judgment (U level) (SortValue (U _)) -> Judgment level (SortValue Level)
getUCodeLevel (UCodeU levelLevel) = levelLevel
getUCodeLevel (LiftCodeU code) = getUCodeLevel code

||| If we have a bad judgment of a given term and sort pair, there is no valid judgment of that term having that sort
||| @ badJudgment The proof that `term` cannot be assigned `sort`
public
badJudgmentNotJudgment : (badJudgment : BadJudgment term sort) -> Not (Judgment term sort)

badJudgmentNotJudgment LevelNotValue (LiftCodeU levelU) = levelNotU levelU where
  levelNotU : Not (Judgment Level (SortValue (U _)))
  levelNotU (LiftCodeU levelU) = levelNotU levelU

badJudgmentNotJudgment SuccLevelNotType (InterpretCodeType (LiftCodeU succLevelU)) = absurd succLevelU
badJudgmentNotJudgment SuccLevelNotU (LiftCodeU succLevelU) = absurd succLevelU
badJudgmentNotJudgment (SuccLevelArgumentNotLevel levelNotLevel) (SuccLevelLevel levelLevel) = badJudgmentNotJudgment levelNotLevel levelLevel

badJudgmentNotJudgment (UArgumentNotLevel notLevel) (UType levelLevel) = badJudgmentNotJudgment notLevel levelLevel
badJudgmentNotJudgment (UArgumentNotLevel notLevel) (InterpretCodeType codeU) = badJudgmentNotJudgment notLevel (getUCodeLevel codeU)
badJudgmentNotJudgment (UArgumentNotLevel notLevel) (UCodeU levelLevel) = badJudgmentNotJudgment notLevel levelLevel
badJudgmentNotJudgment (UArgumentNotLevel notLevel) (LiftCodeU codeU) = badJudgmentNotJudgment notLevel (getUCodeLevel codeU)
badJudgmentNotJudgment (UNotLevel) (SuccLevelLevel _) impossible

badJudgmentNotJudgment (TypeNotType typeNotType) (SuccLevelLevel levelLevel) = badJudgmentNotJudgment typeNotType LevelType
badJudgmentNotJudgment (TypeNotType typeNotType) (UCodeU levelLevel) = badJudgmentNotJudgment typeNotType (UType (SuccLevelLevel levelLevel))
badJudgmentNotJudgment (TypeNotType typeNotType) (LiftCodeU codeU) = badJudgmentNotJudgment typeNotType (UType (SuccLevelLevel (getLevel codeU))) where
  getLevel : Judgment code (SortValue (U level)) -> Judgment level (SortValue Level)
  getLevel (UCodeU levelLevel) = SuccLevelLevel levelLevel
  getLevel (LiftCodeU codeU) = SuccLevelLevel (getLevel codeU)

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
decideJudgment : (term : Term) -> (sort : Sort) -> JudgmentDecision term sort

-- Level type
decideJudgment Level SortType = Good LevelType
decideJudgment Level (SortValue _) = Bad LevelNotValue

-- Level successor
decideJudgment (SuccLevel _) SortType = Bad SuccLevelNotType
decideJudgment _ (SortValue (SuccLevel _)) = Bad (TypeNotType SuccLevelNotType)
decideJudgment (SuccLevel _) (SortValue (U _)) = Bad SuccLevelNotU
decideJudgment (SuccLevel level) (SortValue Level) with (decideJudgment level (SortValue Level))
  | Good judgment = Good (SuccLevelLevel judgment)
  | Bad notLevel = Bad (SuccLevelArgumentNotLevel notLevel)

-- Universe type and code
decideJudgment (U level) SortType with (decideJudgment level (SortValue Level))
  | Good judgment = Good (UType judgment)
  | Bad notLevel = Bad (UArgumentNotLevel notLevel)
decideJudgment (U level) (SortValue Level) = Bad UNotLevel
decideJudgment (U level1) (SortValue (U level2)) = ?hole
