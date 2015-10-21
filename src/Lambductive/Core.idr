||| The lambductive core calculus
module Lambductive.Core

%default total

||| Terms of the language
public
data Term : Type where
  ||| Tarski-style universe
  |||
  ||| The level is marked for erasure because as long as a term typechecks
  ||| we don't care about what universe we're talking about
  ||| @ level The universe's level.
  U : .(level : Nat) -> Term

||| Judgments about terms
public
data Judgment : Type where
  ||| The term is a type
  JudgmentType : Judgment
  ||| The term is a value
  ||| @ type The type of the value
  JudgmentValue : (type : Term) -> Judgment

||| A proof of the validity of a judgment
||| @ term The term we're judging
||| @ judgment The judgment whose validity we're proving
public
data ValidJudgment : (term : Term) -> (judgment : Judgment) -> Type where
  ||| Universes are types
  UType : ValidJudgment (U level) JudgmentType
