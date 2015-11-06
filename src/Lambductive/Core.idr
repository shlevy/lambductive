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
  ||| @levelIsLevel Proof that the level is a level in the context
  UIsType : (levelIsLevel : HasLevelType level context) -> IsType (U level) context
  ||| A dependent function type is a type in any context where its domain is a type and its range is a type in the domain type-augmented context
  ||| @domainIsType Proof that the domain is a type in the context
  ||| @rangeIsType Proof that the range is a type in the domain type-augmented context
  PiIsType : (domainIsType : IsType domain context) -> (rangeIsType : IsType range (domain :: context)) -> IsType (Pi domain range) context
  ||| `Var Z` is a type in any context whose head is a universe
  ||| @levelIsLevel Proof that the universe's level is a level in the context
  VarHeadIsType : (levelIsLevel : HasLevelType level context) -> IsType (Var Z) ((::) (U level) context {headIsType=UIsType levelIsLevel})
  ||| If `Var k` is a type in a context, `Var (S k)` is a type in a context with an extra variable
  ||| @typeIsType Proof that the new type is a type in the old context
  ||| @predIsType Proof that the predecessor var is a type in the old context
  VarTailIsType : (typeIsType : IsType type context) -> (predIsType : IsType (Var k) context) -> IsType (Var (S k)) (type :: context)

||| Proof that a term is a level in a context
||| @term The term in question
||| @context The context in question
data HasLevelType : (term : Term) -> (context : Context) -> Type where
  ||| If a level is a level in a context, its successor is a level in that context
  ||| @levelIsLevel Proof that the level is a level in the context
  SuccLevelHasLevelType : (levelIsLevel : HasLevelType level context) -> HasLevelType (SuccLevel level) context
  ||| `Var Z` is a level in any context whose head is the level type
  VarHeadHasLevelType : HasLevelType (Var Z) (Level :: context)
  ||| If `Var k` is a level in a context, `Var (S k)` is a level in a context with an extra variable
  ||| @typeIsType Proof that the new variable's type is a type in the old context
  ||| @predIsType Proof that the predecessor variable's type is a type in the old context
  VarTailHasLevelType : (typeIsType : IsType type context) -> (predIsType : HasLevelType (Var k) context) -> HasLevelType (Var (S k)) (type :: context)
