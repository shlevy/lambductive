||| Proofs about the calculus
module Lambductive.Proof

import Lambductive.Core

%default total

data LiftCodeView : Nat -> Nat -> Type where
  Sum : (level : Nat) -> LiftCodeView lift (S (lift + level))
  NotSum : (contra : (level1 : Nat) -> Not (level = S (lift + level1))) -> LiftCodeView lift level

liftCodeView : (lift : Nat) -> (level : Nat) -> LiftCodeView lift level
liftCodeView n Z = NotSum zNotSum where
  zNotSum _ Refl impossible
liftCodeView Z (S k) = Sum k
liftCodeView (S n) (S m) with (liftCodeView n m)
  liftCodeView (S n) (S (S (plus n level))) | Sum level = Sum level
  | NotSum contra = NotSum succNotSumNotSum where
    succNotSumNotSum l prf = contra l (succInjective m (S (plus n l)) prf)

decomposeLevel : ValidJudgment (LiftCode lift term) (JudgmentValue (U level)) -> (level1 ** level = S (plus lift level1))
decomposeLevel (LiftCodeU (UCodeU {level})) = ((S level) ** Refl)
decomposeLevel (LiftCodeU (LiftCodeU {lift} {level} term)) = ((S (plus lift level)) ** Refl)

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
  | No contra = No (universeCodeNotInNotSuccUniverse level1 level2 contra) where
    universeCodeNotInNotSuccUniverse _ _ contra (UCodeU) = contra Refl
validJudgment (LiftCode _ _) JudgmentType = No liftCodeNotType where
  liftCodeNotType UType impossible
validJudgment (LiftCode _ _) (JudgmentValue (UCode _)) = No liftCodeNotUniverseCode where
  liftCodeNotUniverseCode UCodeU impossible
validJudgment (LiftCode _ _) (JudgmentValue (LiftCode _ _)) = No liftCodeNotLiftCode where
  liftCodeNotLiftCode UCodeU impossible
validJudgment (LiftCode lift term) (JudgmentValue (U level)) with (liftCodeView lift level)
  validJudgment (LiftCode lift term) (JudgmentValue (U (S (plus lift level1)))) | Sum level1 with (validJudgment term (JudgmentValue (U level1)))
    | Yes judgment = Yes (LiftCodeU judgment)
    | No contra = No (liftCodeNotUNotU lift level1 contra) where
      liftCodeNotUNotU lift level contra judgment with (plus lift level)
        liftCodeNotUNotU lift level contra (LiftCodeU {lift} {level} judgment1) | (plus lift level) = contra judgment1
  | NotSum contra = No (liftCodeNotSmallU lift level contra) where
    liftCodeNotSmallU lift level contra judgment with (decomposeLevel judgment)
      liftCodeNotSmallU lift (S (plus lift level1)) contra judgment | (level1 ** Refl) = contra level1 Refl
