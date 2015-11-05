||| Lambductive core calculus
module Lambductive.Core

%default total

mutual
  ||| DeBruijn variable context
  data Context : Type where
    ||| The empty context
    Nil : Context
    ||| Add a new variable to the context
    ||| @head The type of the new variable
    ||| @tail The context we're adding to
    ||| @headType A proof that `head` is a type
    ||| @headInContext A proof that `head` is in the context we're adding to
    (::) : (head : Term) -> (tail : Context) -> .{auto headType : IsType head} -> .{auto headInContext : InContext head tail} -> Context

  ||| Terms of the calculus
  data Term : Type where
    ||| The type universe
    U : Term
    ||| Dependent function type
    ||| @domain The domain of the function
    ||| @domainType Proof that the domain is a type
    ||| @domainContext Proof that the domain is in a context
    ||| @range The range of the function
    ||| @rangeType Proof that the range is a type
    ||| @rangeContext Proof that the range is in the context obtained by adding a variable of the domain type to the context of the domain
    Pi : (domain : Term) ->
         .{auto domainType : IsType domain} ->
         .{auto domainContext : InContext domain context} ->
         (range : Term) ->
         .{auto rangeType : IsType range} ->
         .{auto rangeContext : InContext range (domain :: context)} ->
         Term

  ||| Proof that a term is a type
  ||| @ term The term in question
  data IsType : (term : Term) -> Type where
    ||| The type universe is a type
    UIsType : IsType U
    ||| Dependent function types are types
    PiIsType : IsType (Pi domain {domainType} {domainContext} range {rangeType} {rangeContext})

  ||| Proof that a term is in a context
  ||| @term The term in question
  ||| @context The context in question
  data InContext : (term : Term) -> (context : Context) -> Type where
    ||| The type universe is in any context
    ||| @context The context the universe is in
    UInAnyContext : InContext U context
    ||| Dependent function types are in the context of their domain
    ||| @domainInContext Proof that the domain is in a context
    PiInDomainContext : (domainInContext : InContext domain context) -> InContext (Pi domain {domainType} range {rangeType} {rangeContext}) context
