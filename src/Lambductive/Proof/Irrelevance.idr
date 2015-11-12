||| Proofs of the computational irrelevance of certain proof terms
module Lambductive.Proof.Irrelevance

import Lambductive.Core

%default total

lteIrrelevant : (a : LTE x y) -> (b : LTE x y) -> a = b
lteIrrelevant LTEZero LTEZero = Refl
lteIrrelevant (LTESucc a) (LTESucc b) with (lteIrrelevant a b)
  lteIrrelevant (LTESucc a) (LTESucc a) | Refl = Refl

levelLTIrrelevant : (a : LevelLT x y) -> (b : LevelLT x y) -> a = b
levelLTIrrelevant LTSmallerBigger LTSmallerBigger = Refl
levelLTIrrelevant (LTSmaller a) (LTSmaller b) with (lteIrrelevant a b)
  levelLTIrrelevant (LTSmaller a) (LTSmaller a) | Refl = Refl
levelLTIrrelevant (LTBigger a) (LTBigger b) with (lteIrrelevant a b)
  levelLTIrrelevant (LTBigger a) (LTBigger a) | Refl = Refl

instance Uninhabited (LTE (S x) x) where
  uninhabited (LTESucc p) = uninhabited p

instance Uninhabited (LevelLT l l) where
  uninhabited (LTSmaller a) = absurd a
  uninhabited (LTBigger a) = absurd a

levelLTEIrrelevant : (a : LevelLTE x y) -> (b : LevelLTE x y) -> a = b
levelLTEIrrelevant LTERefl LTERefl = Refl
levelLTEIrrelevant (LTELT a) (LTELT b) with (levelLTIrrelevant a b)
  levelLTEIrrelevant (LTELT a) (LTELT a) | Refl = Refl
levelLTEIrrelevant (LTELT a) LTERefl = absurd a
levelLTEIrrelevant LTERefl (LTELT a) = absurd a

typeNotUIrrelevant : (a : TypeNotU term) -> (b : TypeNotU term) -> a = b
typeNotUIrrelevant PiType PiType = Refl
typeNotUIrrelevant VarType VarType = Refl

varIdxInBounds : VarSort n c s -> LTE (S n) (length c)
varIdxInBounds VarSortLastValue = lteRefl
varIdxInBounds (VarSortLastType _) = lteRefl
varIdxInBounds (VarSortCons p) = lteSuccRight (varIdxInBounds p)

varSortIrrelevant : (a : VarSort n c s) -> (b : VarSort n c s) -> a = b
varSortIrrelevant (VarSortLastType l1) (VarSortLastType l2) with (levelLTEIrrelevant l1 l2)
  varSortIrrelevant (VarSortLastType l1) (VarSortLastType l1) | Refl = Refl
varSortIrrelevant VarSortLastValue VarSortLastValue = Refl
varSortIrrelevant (VarSortCons a) (VarSortCons b) with (varSortIrrelevant a b)
  varSortIrrelevant (VarSortCons a) (VarSortCons a) | Refl = Refl
varSortIrrelevant (VarSortCons a) (VarSortLastType _) = absurd (varIdxInBounds a)
varSortIrrelevant (VarSortLastType _) (VarSortCons a) = absurd (varIdxInBounds a)
varSortIrrelevant (VarSortCons a) VarSortLastValue = absurd (varIdxInBounds a)
varSortIrrelevant VarSortLastValue (VarSortCons a) = absurd (varIdxInBounds a)
