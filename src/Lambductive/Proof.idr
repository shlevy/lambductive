||| Proofs about the calculus
module Lambductive.Proof

import Lambductive.Core.Term
import Lambductive.Core.Equivalence
import Lambductive.Core.Judgment

%default total

||| The type of a value is of sort `type`
||| @ value The value whose type's sort we're judging
public
valueTypeType : (value : Judgment _ (SortValue type)) -> Judgment type SortType
valueTypeType UCodeU = UType
valueTypeType (LiftCodeU _) = UType

instance Uninhabited (Judgment (UCode _) SortType) where
  uninhabited UCodeU impossible

instance Uninhabited (Judgment (LiftCode _ _) SortType) where
  uninhabited (LiftCodeU _) impossible

||| Transport a judgment along an equivalence
||| @ equivalence The equivalence we're transporting along
||| @ judgment The judgment we're transporting
public
transportJudgment : (equivalence : Equivalence term1 term2) -> (judgment : Judgment term1 sort) -> Judgment term2 sort
transportJudgment InterpretUCodeIsU (InterpretCodeType _) = UType
transportJudgment (LiftCodeCongruence equivalence) (LiftCodeU judgment) with (transportJudgment equivalence judgment)
  | judgment2 = LiftCodeU judgment2

||| A decision procedure for sort judgment
||| @ term The term we're deciding about
||| @ sort The sort we're deciding applies to `term` or not
public
judgmentDecidable : (term : Term) -> (sort : Sort) -> Dec (Judgment term sort)

-- Universes
judgmentDecidable (U _) SortType = Yes UType
judgmentDecidable (U _) (SortValue _) = No universeNotValue where
  universeNotValue UType impossible

-- Universe type code
judgmentDecidable (UCode _) SortType = No absurd
judgmentDecidable _ (SortValue (UCode _)) = No (absurd . valueTypeType)
judgmentDecidable (UCode _) (SortValue (InterpretCode _ _)) = No universeCodeNotInterpretCode where
  universeCodeNotInterpretCode UCodeU impossible
judgmentDecidable (UCode level1) (SortValue (U level2)) with (decEq (S level1) level2)
  judgmentDecidable (UCode level1) (SortValue (U _)) | Yes Refl = Yes UCodeU
  | No contra = No (universeCodeNotNotSuccU level1 level2 contra) where
    universeCodeNotNotSuccU _ _ contra (UCodeU) = contra Refl

-- Universe lift operator
judgmentDecidable (LiftCode _ _) SortType = No absurd
judgmentDecidable _ (SortValue (LiftCode _ _)) = No (absurd . valueTypeType)
judgmentDecidable (LiftCode _ _) (SortValue (InterpretCode _ _)) = No liftCodeNotInterpretCode where
  liftCodeNotInterpretCode (LiftCodeU _) impossible
judgmentDecidable (LiftCode level1 term) (SortValue (U level2)) with (decEq (S level1) level2)
  judgmentDecidable (LiftCode level1 term) (SortValue (U _)) | Yes Refl with (judgmentDecidable term (SortValue (U level1)))
    | Yes judgment = Yes (LiftCodeU judgment)
    | No contra = No (liftCodeNotUNotU level1 contra) where
      liftCodeNotUNotU _ contra (LiftCodeU judgment) = contra judgment
  | No contra = No (liftCodeNotNotSuccU level1 level2 contra) where
    liftCodeNotNotSuccU _ _ contra (LiftCodeU _) = contra Refl

-- Universe interpretation operator
judgmentDecidable (InterpretCode level code) SortType with (judgmentDecidable code (SortValue (U level)))
  | Yes judgment = Yes (InterpretCodeType judgment)
  | No contra = No interpretCodeNotUNotType where
    interpretCodeNotUNotType (InterpretCodeType judgment) = contra judgment
judgmentDecidable (InterpretCode _ _) (SortValue _) = No interpretCodeNotValue where
  interpretCodeNotValue (InterpretCodeType _) impossible
