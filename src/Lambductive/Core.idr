||| Lambductive core calculus
module Lambductive.Core

%default total

||| The infinite hierarchy of universe levels
data Level : Type where
  ||| The increasing side of the hierarchy
  |||
  ||| A bigger `distance` means a bigger level
  ||| @distance The distance from the smallest `Bigger` level
  Bigger : (distance : Nat) -> Level
  ||| The decreasing side of the hierarchy
  |||
  ||| A bigger `distance` means a smaller level
  ||| @distance The (negative) distance from the biggest `Samller` level
  Smaller : (distance : Nat) -> Level

||| The successor of a level
S : Level -> Level
S (Bigger n) = Bigger (S n)
S (Smaller Z) = Bigger Z
S (Smaller (S k)) = Smaller k

||| The bigger of two levels
max : Level -> Level -> Level
max (Bigger n) (Smaller _) = Bigger n
max (Smaller _) (Bigger n) = Bigger n
max (Bigger n) (Bigger m) = Bigger (max n m)
max (Smaller n) (Smaller m) = Smaller (min n m)

||| A judgment of whether a term is a type
data TypeJudgment : Type where
  ||| The term is a type
  ||| @level The level of the universe the term belongs to
  IsType : (level : Level) -> TypeJudgment
  ||| The term is not a type
  NotType : TypeJudgment

data Context : Type

data Term : Context -> TypeJudgment -> Type

||| The variable context of the term
data Context : Type where
  ||| The empty context
  Nil : Context
  ||| Add a variable to an existing context
  ||| @context The existing context
  ||| @type The type of the new variable
  (::) : (context : Context) -> (type : Term context (IsType level)) -> Context

||| An index is in the bounds of a context
||| @idx The index
data InContextBounds : (idx : Nat) -> Context -> Type where
  ||| Zero is in bounds of any non-empty context
  InBoundsZ : InContextBounds Z (context :: type)
  ||| Adding a variable to a context makes one more index in bounds
  InBoundsS : InContextBounds n context -> InContextBounds (S n) (context :: type)

||| Determine if a variable is a type in a context
||| @idx The index of the variable
||| @context The context of the variable
||| @ok `idx` is in the bounds of `context`
varIsType : (idx : Nat) -> (context : Context) -> .{auto ok : InContextBounds idx context} -> TypeJudgment

||| Terms of the calculus
data Term : Context -> TypeJudgment -> Type where
  ||| A type universe
  ||| @level The level of the universe
  U : (level : Level) -> Term context (IsType (S level))
  ||| A dependent function type
  ||| @domain The domain of the function
  ||| @range The (possibly dependent) range of the function
  Pi : (domain : Term context (IsType domainLevel)) ->
       (range : Term (context :: domain) (IsType rangeLevel)) ->
       Term context (IsType (max domainLevel rangeLevel))
  ||| A De Bruijn variable
  ||| @idx The index of the variable in its context
  ||| @ok `idx` is in bounds of context
  Var : (idx : Nat) -> .{auto ok : InContextBounds idx context} -> Term context (varIsType idx context)

varIsType Z (_ :: (U level)) = IsType level
varIsType Z (_ :: _) = NotType
varIsType (S k) (context :: _) {ok=InBoundsS _} = varIsType k context
