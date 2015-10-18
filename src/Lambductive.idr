||| The lambductive core calculus
module Lambductive

%default total

data Context : Type

data Judgment : Context -> Type

data Term : (context : Context) -> Judgment context -> Type

data Contains : Context -> Context -> Type

||| Term judgments
||| @ context The context of the judgment
public data Judgment : (context : Context) -> Type where
  ||| Γ |- T Type
  JudgmentType : Judgment context
  ||| Γ |- T Type -> superset(Γ) |- t : T
  ||| @ type The type of the value
  JudgmentValue : (type: Term typeContext JudgmentType) -> .{auto prf : Contains valueContext typeContext} -> Judgment valueContext

||| Alias for terms that are types
||| @ context The context of the term
public
TypeTerm : (context : Context) -> Type
TypeTerm context = Term context JudgmentType

||| Alias for terms that are values
||| @ context The context of the term
||| @ type The type of the term
public
ValueTerm : (context : Context) -> (type : TypeTerm typeContext) -> {auto prf : Contains context typeContext} -> Type
ValueTerm context type = Term context (JudgmentValue type)

||| Term context, with de Bruijn indexed variables
public data Context : Type where
  ||| []
  Nil : Context
  ||| Γ |- T Type -> (t : T) :: superset(Γ)
  ||| @ type The type of the new variable
  ||| @ context The initial context
  (::) : (type : TypeTerm typeContext) -> (context : Context) -> .{auto prf : Contains context typeContext} -> Context

||| A context contains another context
|||
||| Any term or judgment in a subset can be referenced by a term or judgment in the superset. This allows us to forgo a function lifting terms and judgments into contexts with new variables.
||| @ superset The containing context
||| @ subset The contained context
public data Contains : (superset : Context) -> (subset : Context) -> Type where
  ||| A context contains itself
  ContainsSelf : Contains context context
  ||| If a context contains another context, the first context with an extra variable at the head also contains the second context
  ||| @ type The type of the new variable at the head of the first context
  ||| @ recursiveProof The proof that the first context contains the second context
  ContainsCons : (type : TypeTerm typeContext) -> (recursiveProof : Contains context1 context2) -> .{auto prf : Contains context1 typeContext} -> Contains (type :: context1) context2

||| Any context contains the empty context
||| @ context The context containing the empty context
public
containsNil : Contains context []
containsNil {context=Nil} = ContainsSelf
containsNil {context = type :: _} = ContainsCons type containsNil

||| Terms
||| @ context The context of the term
||| @ judgment The judgment carried by the term
public data Term : (context : Context) -> (judgment : Judgment context) -> Type where
