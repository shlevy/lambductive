||| Proofs about the calculus
module Lambductive.Proof

import Lambductive.Core

%default total

||| A decision procedure for validity
||| @ term The term we're deciding about
||| @ judgment The judgment we're deciding about
public
validJudgment : (term : Term) -> (judgment : Judgment) -> Dec (ValidJudgment term judgment)
validJudgment (U _) JudgmentType = Yes UType
validJudgment (U _) (JudgmentValue _) = No universeNotValue where
  universeNotValue UType impossible
validJudgment (UCode _) JudgmentType = No universeCodeNotType where
  universeCodeNotType UType impossible
validJudgment (UCode _) (JudgmentValue (UCode _)) = No universeCodeNotUniverseCode where
  universeCodeNotUniverseCode UCodeU impossible
validJudgment (UCode _) (JudgmentValue (LiftCode _ _)) = No universeCodeNotLiftCode where
  universeCodeNotLiftCode UCodeU impossible
validJudgment (UCode level1) (JudgmentValue (U level2)) with (decEq (S level1) level2)
  validJudgment (UCode level1) (JudgmentValue (U _)) | Yes Refl = Yes UCodeU
  | No contra = No (universeCodeNotNotSuccU level1 level2 contra) where
    universeCodeNotNotSuccU _ _ contra (UCodeU) = contra Refl
validJudgment (LiftCode _ _) JudgmentType = No liftCodeNotType where
  liftCodeNotType UType impossible
validJudgment (LiftCode _ _) (JudgmentValue (UCode _)) = No liftCodeNotUniverseCode where
  liftCodeNotUniverseCode UCodeU impossible
validJudgment (LiftCode _ _) (JudgmentValue (LiftCode _ _)) = No liftCodeNotLiftCode where
  liftCodeNotLiftCode UCodeU impossible
validJudgment (LiftCode level1 term) (JudgmentValue (U level2)) with (decEq (S level1) level2)
  validJudgment (LiftCode level1 term) (JudgmentValue (U _)) | Yes Refl with (validJudgment term (JudgmentValue (U level1)))
    | Yes judgment = Yes (LiftCodeU judgment)
    | No contra = No (liftCodeNotUNotU level1 contra) where
      liftCodeNotUNotU _ contra (LiftCodeU judgment) = contra judgment
  | No contra = No (liftCodeNotNotSuccU level1 level2 contra) where
    liftCodeNotNotSuccU _ _ contra (LiftCodeU _) = contra Refl
