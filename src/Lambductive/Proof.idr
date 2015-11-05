||| Proofs about the calculus
module Lambductive.Proof

import Lambductive.Core.Term
import Lambductive.Core.Judgment

%default total

data LTE : Term -> Term -> Type where
  LTERefl : Judgment term Level -> LTE term term
  LTESuccRight : LTE level1 level2 -> LTE level1 (SuccLevel level2)
  
LTELeftLevel : LTE term _ -> Judgment term Level
LTELeftLevel (LTERefl judgment) = judgment
LTELeftLevel (LTESuccRight prf) = LTELeftLevel prf

LTERightLevel : LTE _ term -> Judgment term Level
LTERightLevel (LTERefl judgment) = judgment
LTERightLevel (LTESuccRight prf) = SuccLevelIsLevel (LTERightLevel prf)

lteSucc : LTE term1 term2 -> LTE (SuccLevel term1) (SuccLevel term2)
lteSucc (LTERefl judgment) = LTERefl (SuccLevelIsLevel judgment)
lteSucc (LTESuccRight prf) = LTESuccRight (lteSucc prf)

ltePred : LTE (SuccLevel term1) (SuccLevel term2) -> LTE term1 term2
ltePred (LTERefl (SuccLevelIsLevel judgment)) = LTERefl judgment
ltePred (LTESuccRight (LTERefl (SuccLevelIsLevel judgment))) = LTESuccRight (LTERefl judgment)
ltePred (LTESuccRight (LTESuccRight prf)) = LTESuccRight (ltePred (LTESuccRight prf))

instance Uninhabited (Judgment (U _) Level) where
  uninhabited (UIsSuccU _) impossible

instance Uninhabited (Judgment Level _) where
  uninhabited (IsUIsSuccU judgment) = uninhabited judgment

instance Uninhabited (Judgment (Pi _ _) Level) where
  uninhabited (PiIsU _ _) impossible

isLTE : (term1 : Term) -> (term2 : Term) -> Dec (LTE term1 term2)
isLTE (U _) _ = No (absurd . LTELeftLevel)
isLTE _ (U _) = No (absurd . LTERightLevel)
isLTE Level _ = No (absurd . LTELeftLevel)
isLTE _ Level = No (absurd . LTERightLevel)
isLTE (Pi _ _) _ = No (absurd . LTELeftLevel)
isLTE _ (Pi _ _) = No (absurd . LTERightLevel)
isLTE (SuccLevel level1) (SuccLevel level2) with (isLTE level1 level2)
  | Yes prf = Yes (lteSucc prf)
  | No contra = No (contra . ltePred)

||| A structured proof that a given term cannot be assigned a given type
||| @ term The term that is ill-typed
||| @ type The type that does not apply to the terms
public
data IllTyped : (term : Term) -> (type : Term) -> Type where
  ||| `Level` has no type
  LevelNotAnything : IllTyped Level type
  ||| `SuccLevel term` has no type if `term` is not a level
  ||| @ termIsNotLevel Proof that `term` is not a level
  SuccLevelNotLevelNotAnything : (termIsNotLevel : IllTyped term Level) -> IllTyped (SuccLevel term) type
  ||| `SuccLevel term` is not a member of any universe
  SuccLevelNotU : IllTyped (SuccLevel level1) (U level2)
  ||| `SuccLevel term` is not a dependent function type
  SuccLevelNotPi : IllTyped (SuccLevel level) (Pi domain range)
  ||| `SuccLevel term` is not a type
  SuccLevelNotType : IllTyped term (SuccLevel level)
  ||| A universe is not a level
  UNotLevel : IllTyped (U level) Level
  ||| A universe is not a dependent function type
  UNotPi : IllTyped (U level) (Pi domain range)
  ||| A universe is not the type of another universe whose level is not strictly less than the first universe's
  ||| @ succLevelLevel1NotLTELevel2 A proof that the universe's level is not strictly less than its containing universe's level
  NotLTUNotU : .(succLevelLevel1NotLTELevel2 : Not (LTE (SuccLevel level1) level2)) -> IllTyped (U level1) (U level2)
  ||| A dependent function type is not a level
  PiNotLevel : IllTyped (Pi domain range) Level
  ||| A dependent function type whose range is not in a universe is not in that universe
  ||| @ rangeNotU A proof that the range is not in the universe
  PiRangeNotUNotU : (rangeNotU : IllTyped range (U level)) -> IllTyped (Pi domain range) (U level)
  ||| A dependent function type whose domain is not in a universe is not in that universe
  ||| @ domainNotU A proof that the domain is not in the universe
  PiDomainNotUNotU : (domainNotU : IllTyped domain (U level)) -> IllTyped (Pi domain range) (U level)
  ||| A dependent function type is not a dependent function
  PiNotPi : IllTyped (Pi domain1 range1) (Pi domain2 range2)

instance Uninhabited (Judgment (SuccLevel _) (U _)) where
  uninhabited (IsUIsSuccU judgment) = uninhabited judgment

uIsBiggerU : Judgment (U level1) (U level2) -> LTE (SuccLevel level1) level2
uIsBiggerU (UIsSuccU judgment) = lteSucc (LTERefl judgment)
uIsBiggerU (IsUIsSuccU prf) = LTESuccRight (uIsBiggerU prf)

piRangeU : Judgment (Pi _ range) (U level) -> Judgment range (U level)
piRangeU (PiIsU _ rangeIsU) = rangeIsU
piRangeU (IsUIsSuccU piIsU) = IsUIsSuccU (piRangeU piIsU)

piDomainU : Judgment (Pi domain _) (U level) -> Judgment domain (U level)
piDomainU (PiIsU domainIsU _) = domainIsU
piDomainU (IsUIsSuccU piIsU) = IsUIsSuccU (piDomainU piIsU)

||| If a term cannot be assigned a given type, there is no judgment assigning that term that type
||| @termNotType Proof that `term` is not in `type`
abstract
illTypedCorrect : (termNotType : IllTyped term type) -> Not (Judgment term type)
illTypedCorrect LevelNotAnything judgment = absurd judgment
illTypedCorrect (SuccLevelNotLevelNotAnything prf) (SuccLevelIsLevel levelIsLevel) = illTypedCorrect prf levelIsLevel
illTypedCorrect (SuccLevelNotLevelNotAnything _) (IsUIsSuccU judgment) = absurd judgment
illTypedCorrect SuccLevelNotU judgment = absurd judgment
illTypedCorrect (NotLTUNotU contra) judgment = contra (uIsBiggerU judgment)
illTypedCorrect (PiRangeNotUNotU prf) judgment = illTypedCorrect prf (piRangeU judgment)
illTypedCorrect (PiDomainNotUNotU prf) judgment = illTypedCorrect prf (piDomainU judgment)

||| A decision about whether a term can be assigned a type
||| @ term The term we're deciding about
||| @ type The type we're deciding applies to `term` or not
public
data JudgmentDecision : (term : Term) -> (type : Term) -> Type where
  ||| The term can be assigned the type
  ||| @ judgment The judgment assigning `term` the type `type`
  Good : .(judgment : Judgment term type) -> JudgmentDecision term type
  ||| The term cannot be assigned the type
  ||| @ illTyped The proof that `term` cannot be assigned the type `type`
  Bad : (illTyped : IllTyped term type) -> JudgmentDecision term type

succLevelLevel : Judgment (SuccLevel level) Level -> Judgment level Level
succLevelLevel (SuccLevelIsLevel levelIsLevel) = levelIsLevel

uIsBiggerU' : LTE (SuccLevel level1) level2 -> Judgment (U level1) (U level2)
uIsBiggerU' (LTERefl (SuccLevelIsLevel prf)) = UIsSuccU prf
uIsBiggerU' (LTESuccRight (LTERefl prf)) = IsUIsSuccU (UIsSuccU (succLevelLevel prf))
uIsBiggerU' (LTESuccRight (LTESuccRight prf)) = IsUIsSuccU (IsUIsSuccU (uIsBiggerU' prf))

||| A decision procedure for type judgment
||| @ term The term we're deciding about
||| @ type The type we're deciding applies to `term` or not
abstract
decideJudgment : (term : Term) -> (type : Term) -> JudgmentDecision term type

-- Level Type
decideJudgment Level _ = Bad LevelNotAnything

-- Level successor
decideJudgment (SuccLevel level) Level with (decideJudgment level Level)
  | Good levelIsLevel = Good (SuccLevelIsLevel levelIsLevel)
  | Bad levelNotLevel = Bad (SuccLevelNotLevelNotAnything levelNotLevel)
decideJudgment (SuccLevel _) (U _) = Bad SuccLevelNotU
decideJudgment (SuccLevel _) (Pi _ _) = Bad SuccLevelNotPi
decideJudgment _ (SuccLevel _) = Bad SuccLevelNotType

-- Universe
decideJudgment (U level1) (U level2) with (isLTE (SuccLevel level1) level2)
  | No contra = Bad (NotLTUNotU contra)
  | Yes prf = Good (uIsBiggerU' prf)
decideJudgment (U _) Level = Bad UNotLevel
decideJudgment (U _) (Pi _ _) = Bad UNotPi

-- Pi type
decideJudgment (Pi _ _) Level = Bad PiNotLevel
decideJudgment (Pi domain range) (U level) with (decideJudgment domain (U level))
  | Good domainU with (decideJudgment range (U level))
    | Good rangeU = Good (PiIsU domainU rangeU)
    | Bad rangeNotU = Bad (PiRangeNotUNotU rangeNotU)
  | Bad domainNotU = Bad (PiDomainNotUNotU domainNotU)
decideJudgment (Pi _ _) (Pi _ _) = Bad PiNotPi
