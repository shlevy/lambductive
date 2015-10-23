||| Proofs about the calculus
module Lambductive.Proof

import Lambductive.Core

%default total

||| Get the type of a value
||| @ value The value whose type we're extracting
public
getValueType : (value : ValidJudgment term (JudgmentValue type)) -> ValidJudgment type JudgmentType
getValueType UCodeU = UType
getValueType (LiftCodeU _) = UType

universeCodeNotType : ValidJudgment (UCode _) JudgmentType -> Void
universeCodeNotType UType impossible

liftCodeNotType : ValidJudgment (LiftCode _ _) JudgmentType -> Void
liftCodeNotType UType impossible

||| A decision procedure for validity
||| @ term The term we're deciding about
||| @ judgment The judgment we're deciding about
public
validJudgment : (term : Term) -> (judgment : Judgment) -> Dec (ValidJudgment term judgment)

-- Universes
validJudgment (U _) JudgmentType = Yes UType
validJudgment (U _) (JudgmentValue _) = No universeNotValue where
  universeNotValue UType impossible

-- Universe type code
validJudgment (UCode _) JudgmentType = No universeCodeNotType
validJudgment _ (JudgmentValue (UCode _)) = No (universeCodeNotType . getValueType)
validJudgment (UCode _) (JudgmentValue (InterpretCode _ _)) = No universeCodeNotInterpretCode where
  universeCodeNotInterpretCode UCodeU impossible
validJudgment (UCode level1) (JudgmentValue (U level2)) with (decEq (S level1) level2)
  validJudgment (UCode level1) (JudgmentValue (U _)) | Yes Refl = Yes UCodeU
  | No contra = No (universeCodeNotNotSuccU level1 level2 contra) where
    universeCodeNotNotSuccU _ _ contra (UCodeU) = contra Refl

-- Universe lift operator
validJudgment (LiftCode _ _) JudgmentType = No liftCodeNotType
validJudgment _ (JudgmentValue (LiftCode _ _)) = No (liftCodeNotType . getValueType)
validJudgment (LiftCode _ _) (JudgmentValue (InterpretCode _ _)) = No liftCodeNotInterpretCode where
  liftCodeNotInterpretCode UCodeU impossible
validJudgment (LiftCode level1 term) (JudgmentValue (U level2)) with (decEq (S level1) level2)
  validJudgment (LiftCode level1 term) (JudgmentValue (U _)) | Yes Refl with (validJudgment term (JudgmentValue (U level1)))
    | Yes judgment = Yes (LiftCodeU judgment)
    | No contra = No (liftCodeNotUNotU level1 contra) where
      liftCodeNotUNotU _ contra (LiftCodeU judgment) = contra judgment
  | No contra = No (liftCodeNotNotSuccU level1 level2 contra) where
    liftCodeNotNotSuccU _ _ contra (LiftCodeU _) = contra Refl

-- Universe interpretation operator
validJudgment (InterpretCode level code) JudgmentType with (validJudgment code (JudgmentValue (U level)))
  | Yes judgment = Yes (InterpretCodeType judgment)
  | No contra = No interpretCodeNotUNotType where
    interpretCodeNotUNotType (InterpretCodeType judgment) = contra judgment
validJudgment (InterpretCode _ _) (JudgmentValue _) = No interpretCodeNotValue where
  interpretCodeNotValue (InterpretCodeType _) impossible
