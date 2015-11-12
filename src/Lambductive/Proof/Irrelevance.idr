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

instance Uninhabited (SubContext ((::) t c {ok}) c) where
  uninhabited {c=[]} (SubContextCons _) impossible

subContextIrrelevant : (a : SubContext sub super) ->
                       (b : SubContext sub super) ->
                       a = b
subContextIrrelevant SubContextRefl SubContextRefl = Refl
subContextIrrelevant (SubContextCons p1) (SubContextCons p2) with
  (subContextIrrelevant p1 p2)
  subContextIrrelevant (SubContextCons p1) (SubContextCons p1) | Refl = Refl
subContextIrrelevant (SubContextCons p) SubContextRefl = absurd p
subContextIrrelevant SubContextRefl (SubContextCons p) = absurd p

varSortIrrelevant : (a : VarSort n c s) -> (b : VarSort n c s) -> a = b
varSortIrrelevant (VarSortLastType l1) (VarSortLastType l2) with (levelLTEIrrelevant l1 l2)
  varSortIrrelevant (VarSortLastType l1) (VarSortLastType l1) | Refl = Refl
varSortIrrelevant VarSortLastValue VarSortLastValue = Refl
varSortIrrelevant (VarSortCons a) (VarSortCons b) with (varSortIrrelevant a b)
  varSortIrrelevant (VarSortCons a) (VarSortCons a) | Refl = Refl
varSortIrrelevant (VarSortCons a) (VarSortLastType l) = ?hole1
varSortIrrelevant (VarSortLastType l) (VarSortCons b) = ?hole2
varSortIrrelevant (VarSortCons a) VarSortLastValue = ?hole3
varSortIrrelevant VarSortLastValue (VarSortCons b) = ?hole4
