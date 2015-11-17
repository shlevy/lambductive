||| Lambductive core calculus
module Lambductive.Core

%default total

data Context : Type

||| Typing judgments that apply to terms
data TypeJudgment : Type where
  ||| The term is a type
  ||| @level The level of the universe it belongs to
  IsType : (level : Nat) -> TypeJudgment

data Term : Context -> TypeJudgment -> Type

infixl 7 :::

||| Variable context of terms
data Context : Type where
  ||| The empty context
  Nil : Context
  ||| Add a variable to a context
  ||| @type The type of the new variable
  (:::) : (context : Context) -> (type : Term context (IsType level)) -> Context

||| Terms of the calculus
||| @context The context of the term
||| @type The type of the term
data Term : (context : Context) -> (type : TypeJudgment) -> Type where
  ||| A type universe
  U : (level : Nat) -> Term context (IsType (S level))
  ||| A dependent function type
  Pi : (domain : Term context (IsType level)) -> (codomain : Term (context ::: domain) (IsType level)) -> Term context (IsType level)
