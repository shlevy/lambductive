||| Lambductive core calculus
module Lambductive.Core

%default total

data Term : Type

data Context : Type

data IsType : Term -> Context -> Type

||| DeBruijn variable context
data Context : Type where
  ||| The empty context
  Nil : Context
  ||| Add a new variable to the context
  ||| @head The type of the new variable
  ||| @tail The context we're adding to
  ||| @headIsType A proof that `head` is a type in the context
  (::) : (head : Term) -> (tail : Context) -> .{auto headIsType : IsType head tail} -> Context

data HasLevelType : Term -> Context -> Type

||| Terms of the calculus
data Term : Type where
  ||| The type of universe levels
  Level : Term
  ||| The successor of a level
  ||| @level The level whose successor we're computing
  ||| @levelIsLevel Proof that `level` is a level in this context
  SuccLevel : (level : Term) -> .{auto levelIsLevel : HasLevelType level context} -> Term
  ||| The type universe
  ||| @level The universe's level
  ||| @levelIsLevel Proof that `level` is a level
  U : (level : Term) -> .{auto levelIsLevel : HasLevelType level context} -> Term
  ||| Dependent function type
  ||| @domain The domain of the function
  ||| @domainIsType Proof that the domain is a type in the context of the function type
  ||| @range The range of the function
  ||| @rangeIsType Proof that the range is a type in the context obtained by adding a variable of the domain type to the context of the domain
  Pi : (domain : Term) ->
       .{auto domainIsType : IsType domain context} ->
       (range : Term) ->
       .{auto rangeIsType : IsType range (domain :: context)} ->
       Term
  ||| DeBruijn-indexed variable
  ||| @idx The variable index
  Var : (idx : Nat) -> Term

||| The term is a type in the context
||| @term The term in question
||| @context The context in question
data IsType : (term : Term) -> (context : Context) -> Type where
  ||| Level is a type in any context
  LevelIsType : IsType Level context
  ||| The type universe is a type in any context where its level is a level
  UIsType : IsType (U {context} level {levelIsLevel}) context
  ||| A dependent function type is a type in any context where its domain and range are valid
  PiIsType : IsType (Pi {context} domain {domainIsType} range {rangeIsType}) context
  ||| `Var Z` is a type in any context whose head is a universe
  VarHeadIsType : IsType (Var Z) ((::) (U {context} level {levelIsLevel}) context {headIsType})
  ||| If `Var k` is a type in a context, `Var (S k)` is a type in a context with an extra variable
  ||| @predIsType Proof that the predecessor var is a type in the old context
  VarTailIsType : (predIsType : IsType (Var k) context) -> IsType (Var (S k)) ((::) type context {headIsType})

||| Proof that a term is a level in a context
||| @term The term in question
||| @context The context in question
data HasLevelType : (term : Term) -> (context : Context) -> Type where
  ||| If a level is a level in a context, its successor is a level in that context
  SuccLevelHasLevelType : HasLevelType (SuccLevel {context} level {levelIsLevel}) context
  ||| `Var Z` is a level in any context whose head is the level type
  VarHeadHasLevelType : HasLevelType (Var Z) (Level :: context)
  ||| If `Var k` is a level in a context, `Var (S k)` is a level in a context with an extra variable
  ||| @predIsType Proof that the predecessor variable's type is a type in the old context
  VarTailHasLevelType : (predIsType : HasLevelType (Var k) context) -> HasLevelType (Var (S k)) ((::) type context {headIsType})
