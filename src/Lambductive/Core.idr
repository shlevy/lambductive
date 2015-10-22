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
  ||| An asserted axiom
  ||| @ name The name of the axiom
  Axiom : (name : String) -> Term

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
  ||| Axioms are what you say they are
  ||| @ name The name of the axiom
  ||| @ judgment The judgment you're asserting about the axiom
  AxiomAny : ValidJudgment (Axiom name) judgment
