||| Lambductive core calculus
module Lambductive.Core

%default total

||| Judgments made about terms
data Judgment : Type where
  ||| The term is a type
  ||| @varJudgment The judgment that applies to variables of the type
  JudgmentType : (varJudgment : Judgment) -> Judgment
  ||| The term is a value that is not a type
  JudgmentValue : Judgment

data Context : Type

data Term : Context -> Judgment -> Type

infixl 7 :::

||| The variable context of the term
data Context : Type where
  ||| The empty context
  Nil : Context
  ||| Add a variable to an existing context
  ||| @type The type of the new variable
  (:::) : (context : Context) -> (type : Term context (JudgmentType varJudgment)) -> Context

||| Variable indices
||| @context The context indexed into
||| @judgment The judgment of the variable at the index
data VarIndex : (context : Context) -> (judgment : Judgment) -> Type where
  ||| The base variable index
  Z : VarIndex ((:::) context {varJudgment} type) varJudgment
  ||| The successor of a variable index
  S : VarIndex context judgment -> VarIndex (context ::: type) judgment

||| Terms of the calculus
data Term : Context -> Judgment -> Type where
  ||| A type universe
  U : Term context (JudgmentType (JudgmentType JudgmentValue))
  ||| A dependent function type
  Pi : (domain : Term context (JudgmentType domainJudgment)) ->
       (range : Term (context ::: domain) (JudgmentType rangeJudgment)) ->
       Term context (JudgmentType JudgmentValue)
  ||| A De Bruijn variable
  Var : VarIndex context judgment -> Term context judgment
  ||| A lambda abstraction
  ||| @domain The domain of the function type which this lambda inhabits
  Lam : (body : Term (context ::: domain) bodyJudgment) -> Term context JudgmentValue
