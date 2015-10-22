||| The lambductive core calculus
module Lambductive.Core

%default total

||| Terms of the language
public
data Term : Type where
  ||| Tarski-style universe
  ||| @ level The universe's level
  U : (level : Nat) -> Term
  ||| Type code for universe
  ||| @ level The universe's level
  UCode : (level : Nat) -> Term
  ||| Lifting operator for type codes
  ||| @ level The level from which to lift a code
  ||| @ code The code to lift
  LiftCode : (level : Nat) -> (code : Term) -> Term

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
  ||| Universe codes are elements of the next universe
  UCodeU : ValidJudgment (UCode level) (JudgmentValue (U (S level)))
  ||| Lifted codes are elements of the universe they're lifted to
  ||| @ codeU A valid judgment that `code` is an element of some universe
  LiftCodeU : (codeU : ValidJudgment code (JudgmentValue (U level))) -> ValidJudgment (LiftCode level code) (JudgmentValue (U (S level)))
