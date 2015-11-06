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
  ||| @headType A proof that `head` is a type in the context
  (::) : (head : Term) -> (tail : Context) -> .{auto headType : IsType head tail} -> Context

||| Terms of the calculus
data Term : Type where
  ||| The type universe
  U : Term
  ||| Dependent function type
  ||| @domain The domain of the function
  ||| @domainType Proof that the domain is a type in the context of the function type
  ||| @range The range of the function
  ||| @rangeType Proof that the range is a type in the context obtained by adding a variable of the domain type to the context of the domain
  Pi : (domain : Term) ->
       .{auto domainType : IsType domain context} ->
       (range : Term) ->
       .{auto rangeType : IsType range (domain :: context)} ->
       Term
  ||| DeBruijn-indexed variable
  ||| @idx The variable index
  Var : (idx : Nat) -> Term

||| An index is in the bounds of a context
||| @idx The index in question
||| @context The context in question
data InContextBounds : (idx : Nat) -> (context : Context) -> Type where
  ||| Zero is a valid index into any non-empty list
  InFirst : .{auto headType : IsType x xs} -> InContextBounds Z (x :: xs)
  ||| If an index's predecessor is valid into the tail of a list, the index is valid into the list
  ||| @predInTail Proof that the predecessor is in the tail of the list
  InLater : .{auto headType : IsType x xs} -> (predInTail : InContextBounds k xs) -> InContextBounds (S k) (x :: xs)

||| Look up a term from a context
||| @n The index to look up
||| @context The context to index
||| @ok Proof that the index is in bounds
index : (n : Nat) -> (context : Context) -> .{auto ok : InContextBounds n context} -> Term
index Z (x :: xs) {ok} = x
index (S k) (x :: xs) {ok = InLater p} = index k xs

||| Drop some terms from a context
|||
||| `drop` is saturating: Dropping anything from an empty context yields an empty context
||| @n The number of terms to drop
||| @context The context to drop from
drop : (n : Nat) -> (context : Context) -> Context
drop Z context = context
drop _ [] = []
drop (S k) (x :: xs) = drop k xs

||| Proof that a term is a universe
||| @term The term in question
data IsU : (term : Term) -> Type where
  ||| The universe is a universe
  UIsU : IsU U

||| Proof that a term is a type in a context
||| @term The term in question
||| @context The context of the term
data IsType : (term : Term) -> (context : Context) -> Type where
  ||| The type universe is a type
  UIsType : IsType U context
  ||| Dependent function types are types
  ||| @domainType Proof that the domain is a type in the context of the function type
  ||| @rangeType Proof that the range is a type in the context obtained by adding a variable of the domain type to the context of the domain
  PiIsType : .{auto domainType : IsType domain context} -> .{auto rangeType : IsType range (domain :: context)} -> IsType (Pi domain range) context
  ||| Vars whose types are universes are types
  ||| @ok Proof that the variable index is in bounds
  ||| @typeIsU Proof that the variable type is a universe
  VarIsUIsType : .{auto ok : InContextBounds idx context} -> (typeIsU : IsU (index idx context)) -> IsType (Var idx) context
