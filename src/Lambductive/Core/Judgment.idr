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
  ||| Level is a type
  LevelType : Judgment Level SortType
  ||| The successor of a level is a level
  ||| @ levelLevel A judgment that `level` is a level
  SuccLevelLevel : (levelLevel : Judgment level (SortValue Level)) -> Judgment (SuccLevel level) (SortValue Level)
  ||| Universes are types
  ||| @ levelLevel A judgment that `level` is a level
  UType : (levelLevel : Judgment level (SortValue Level)) -> Judgment (U level) SortType
  ||| Universe codes are elements of the next universe
  ||| @ levelLevel A judgment that `level` is a level
  UCodeU : (levelLevel : Judgment level (SortValue Level)) -> Judgment (U level) (SortValue (U (SuccLevel level)))
  ||| Lifted codes are elements of the universe they're lifted to
  ||| @ codeU A judgment that `code` is an element of some universe
  LiftCodeU : (codeU : Judgment code (SortValue (U level))) -> Judgment code (SortValue (U (SuccLevel level)))
  ||| Interpreted codes are types
  |||
  ||| For equivalences to stay simple, this requires the term for a type's code, if any, to be the same as the term for the type it represents.
  ||| @ codeU A judgment that `code` is an element of some universe
  InterpretCodeType : (codeU : Judgment code (SortValue (U level))) -> Judgment code SortType
