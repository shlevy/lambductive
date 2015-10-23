||| Judgments of the calculus
module Lambductive.Core.Judgment

import Lambductive.Core.Term

%default total

||| Sorts of terms
public
data Sort : Type where
  ||| The term is a type
  SortType : Sort
  ||| The term is a value
  ||| @ type The type of the value
  SortValue : (type : Term) -> Sort

||| A judgment of the sort of the term
||| @ term The term we're judging
||| @ sort The sort we're assigning to the term
public
data Judgment : (term : Term) -> (sort : Sort) -> Type where
  ||| Universes are types
  UType : Judgment (U level) SortType
  ||| Universe codes are elements of the next universe
  UCodeU : Judgment (UCode level) (SortValue (U (S level)))
  ||| Lifted codes are elements of the universe they're lifted to
  ||| @ codeU A judgment that `code` is an element of some universe
  LiftCodeU : (codeU : Judgment code (SortValue (U level))) -> Judgment (LiftCode level code) (SortValue (U (S level)))
  ||| Interpreted codes are types
  ||| @ codeU A judgment that `code` is an element of some universe
  InterpretCodeType : (codeU : Judgment code (SortValue (U level))) -> Judgment (InterpretCode level code) SortType
