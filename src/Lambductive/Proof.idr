||| Proofs about the calculus
module Lambductive.Proof

import Lambductive.Core.Term
import Lambductive.Core.Judgment

%default total

||| A structured proof that a given term cannot be judged to have a given sort
||| @ term The term we're judging
||| @ sort The sort that cannot be assigned
public
data BadJudgment : (term : Term) -> (sort : Sort) -> Type where
  ||| The Level type is not a value
  LevelNotValue : BadJudgment Level (SortValue type)

  ||| The successor of a level is not a type
  SuccLevelNotType : BadJudgment (SuccLevel level) SortType
  ||| The successor level of a term that is not a level is not a level
  ||| @ levelNotLevel Proof that `level` is not a level
  SuccLevelArgumentNotLevel : (levelNotLevel : BadJudgment level (SortValue Level)) -> BadJudgment (SuccLevel level) (SortValue Level)
  ||| The successor of a level is not a type code
  SuccLevelNotU : BadJudgment (SuccLevel level1) (SortValue (U level2))
  ||| The successor of a level is not a member of any interpreted code
  SuccLevelNotInterpretCode : BadJudgment (SuccLevel level1) (SortValue (InterpretCode level2 code))

  ||| The universe of a term that is not a level is not a universe
  ||| @ levelNotLevel Proof that `level` is not a level
  UArgumentNotLevel : (levelNotLevel : BadJudgment level (SortValue Level)) -> BadJudgment (U level) SortType
  ||| The universe is not a value
  UNotValue : BadJudgment (U level) (SortValue type)

  ||| The universe code is not a type
  UCodeNotType : BadJudgment (UCode level) SortType
  ||| The universe code is not a level
  UCodeNotLevel : BadJudgment (UCode level) (SortValue Level)
  ||| The code of a universe of a term that is not a level is not a universe code
  ||| @ levelNotLevel Proof that `level` is not a level
  UCodeArgumentNotLevel : (levelNotLevel : BadJudgment level (SortValue Level)) -> BadJudgment (UCode level) (SortValue (U (SuccLevel level)))
  ||| If a universe's level is not the successor of the universe code's, the code does not belong to that universe
  ||| @ succLevel1NotLevel2 Proof that the successor of `level1` is not `level2`
  UCodeNotNotSuccU : (succLevel1NotLevel2 : Not (SuccLevel level1 = level2)) -> BadJudgment (UCode level1) (SortValue (U level2))
  ||| A universe code is not a member of any interpreted code (for now)
  UCodeNotInterpretCode : BadJudgment (UCode level1) (SortValue (InterpretCode level2 code))

  ||| If a code is not a member of a given universe, the interpretation of that code from that universe is not a type
  ||| @ codeNotU Proof that `code` is not a code of the universe
  InterpretCodeArgumentNotU : (codeNotU : BadJudgment code (SortValue (U level))) -> BadJudgment (InterpretCode level code) SortType
  ||| The interpretation of a universe code is not a value
  InterpretCodeNotValue : BadJudgment (InterpretCode level code) (SortValue type)

  ||| A lifted code is not a type
  LiftCodeNotType : BadJudgment (LiftCode level code) SortType
  ||| A lifted code is not a level
  LiftCodeNotLevel : BadJudgment (LiftCode level code) (SortValue Level)
  ||| If a code is not a member of a given universe, the lift of that code from that universe is not a member of the next universe
  ||| @ codeNotU Proof that `code` is not a code of the universe
  LiftCodeArgumentNotU : (codeNotU : BadJudgment code (SortValue (U level))) -> BadJudgment (LiftCode level code) (SortValue (U (SuccLevel level)))
  ||| If a universe's level is not the successor of the lift operator's, the lifted code does not belong to that universe
  ||| @ succLevel1NotLevel2 Proof that the successor of `level1` is not `level2`
  LiftCodeNotNotSuccU : (succLevel1NotLevel2 : Not (SuccLevel level1 = level2)) -> BadJudgment (LiftCode level1 code) (SortValue (U level2))
  ||| A lifted code is not a member of any interpreted code (for now)
  LiftCodeNotInterpretCode : BadJudgment (LiftCode level1 code1) (SortValue (InterpretCode level2 code2))

  ||| If a value's proposed type is not a type, the value does not have that type
  TypeNotType : (typeNotType : BadJudgment type SortType) -> BadJudgment value (SortValue type)

||| If we have a bad judgment of a given term and sort pair, there is no valid judgment of that term having that sort
||| @ badJudgment The proof that `term` cannot be assigned `sort`
public
badJudgmentNotJudgment : (badJudgment : BadJudgment term sort) -> Not (Judgment term sort)

badJudgmentNotJudgment LevelNotValue LevelType impossible

badJudgmentNotJudgment SuccLevelNotType (SuccLevelLevel _) impossible
badJudgmentNotJudgment (SuccLevelArgumentNotLevel levelNotLevel) (SuccLevelLevel levelLevel) = badJudgmentNotJudgment levelNotLevel levelLevel
badJudgmentNotJudgment SuccLevelNotU (SuccLevelLevel _) impossible
badJudgmentNotJudgment SuccLevelNotInterpretCode (SuccLevelLevel _) impossible

badJudgmentNotJudgment (UArgumentNotLevel levelNotLevel) (UType levelLevel) = badJudgmentNotJudgment levelNotLevel levelLevel
badJudgmentNotJudgment UNotValue (UType _) impossible

badJudgmentNotJudgment UCodeNotType (UCodeU _) impossible
badJudgmentNotJudgment UCodeNotLevel (UCodeU _) impossible
badJudgmentNotJudgment (UCodeArgumentNotLevel levelNotLevel) (UCodeU levelLevel) = badJudgmentNotJudgment levelNotLevel levelLevel
badJudgmentNotJudgment (UCodeNotNotSuccU succLevel1NotLevel2) (UCodeU _) = succLevel1NotLevel2 Refl
badJudgmentNotJudgment UCodeNotInterpretCode (UCodeU _) impossible

badJudgmentNotJudgment (InterpretCodeArgumentNotU codeNotU) (InterpretCodeType codeU) = badJudgmentNotJudgment codeNotU codeU
badJudgmentNotJudgment InterpretCodeNotValue (InterpretCodeType _) impossible

badJudgmentNotJudgment LiftCodeNotType (LiftCodeU _) impossible
badJudgmentNotJudgment LiftCodeNotLevel (LiftCodeU _) impossible
badJudgmentNotJudgment (LiftCodeArgumentNotU codeNotU) (LiftCodeU codeU) = badJudgmentNotJudgment codeNotU codeU
badJudgmentNotJudgment (LiftCodeNotNotSuccU succLevel1NotLevel2) (LiftCodeU _) = succLevel1NotLevel2 Refl
badJudgmentNotJudgment LiftCodeNotInterpretCode (LiftCodeU _) impossible

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
decideJudgment (SuccLevel level) (SortValue Level) with (decideJudgment level (SortValue Level))
  | Good levelLevel = Good (SuccLevelLevel levelLevel)
  | Bad levelNotLevel = Bad (SuccLevelArgumentNotLevel levelNotLevel)
decideJudgment (SuccLevel _) (SortValue (U _)) = Bad SuccLevelNotU
decideJudgment (SuccLevel _) (SortValue (InterpretCode _ _)) = Bad SuccLevelNotInterpretCode

-- Universe type
decideJudgment (U level) SortType with (decideJudgment level (SortValue Level))
  | Good levelLevel = Good (UType levelLevel)
  | Bad levelNotLevel = Bad (UArgumentNotLevel levelNotLevel)
decideJudgment (U level) (SortValue _) = Bad UNotValue

-- Universe code
decideJudgment (UCode _) SortType = Bad UCodeNotType
decideJudgment _ (SortValue (UCode _)) = Bad (TypeNotType UCodeNotType)
decideJudgment (UCode _) (SortValue Level) = Bad UCodeNotLevel
decideJudgment (UCode level1) (SortValue (U level2)) with (decEq (SuccLevel level1) level2)
  decideJudgment (UCode level1) (SortValue (U _)) | Yes Refl with (decideJudgment level1 (SortValue Level))
    | Good level1Level = Good (UCodeU level1Level)
    | Bad levelNotLevel = Bad (UCodeArgumentNotLevel levelNotLevel)
  | No contra = Bad (UCodeNotNotSuccU contra)
decideJudgment (UCode _) (SortValue (InterpretCode _ _)) = Bad UCodeNotInterpretCode

-- Code interpretation operator
decideJudgment (InterpretCode level code) SortType with (decideJudgment code (SortValue (U level)))
  | Good codeU = Good (InterpretCodeType codeU)
  | Bad codeNotU = Bad (InterpretCodeArgumentNotU codeNotU)
decideJudgment (InterpretCode _ _) (SortValue _) = Bad InterpretCodeNotValue

-- Code lifting operator
decideJudgment (LiftCode _ _) SortType = Bad LiftCodeNotType
decideJudgment _ (SortValue (LiftCode _ _)) = Bad (TypeNotType LiftCodeNotType)
decideJudgment (LiftCode _ _) (SortValue Level) = Bad LiftCodeNotLevel
decideJudgment (LiftCode level1 code) (SortValue (U level2)) with (decEq (SuccLevel level1) level2)
  decideJudgment (LiftCode level1 code) (SortValue (U _)) | Yes Refl with (decideJudgment code (SortValue (U level1)))
    | Good codeU = Good (LiftCodeU codeU)
    | Bad codeNotU = Bad (LiftCodeArgumentNotU codeNotU)
  | No contra = Bad (LiftCodeNotNotSuccU contra)
decideJudgment (LiftCode _ _) (SortValue (InterpretCode _ _)) = Bad LiftCodeNotInterpretCode
