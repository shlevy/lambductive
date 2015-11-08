||| Lambductive core calculus
module Lambductive.Core

%default total

data Context : Type

data Term : Context -> Type

data IsType : Term context -> Type

||| DeBruijn variable context
data Context : Type where
  ||| The empty context
  Nil : Context
  ||| Add a new variable to the context
  ||| @context The existing context
  ||| @type The type of the new variable
  ||| @typeIsType Proof that `type` is a type
  Snoc : (context : Context) -> (type : Term context) -> .{auto typeIsType : IsType type} -> Context

data HasLevelType : Term context -> Type

||| Terms of the calculus
||| @context The context of the term
data Term : (context : Context) -> Type where
  ||| The type of universe levels
  Level : Term context
  ||| The successor of a level
  ||| @level The level whose successor we're computing
  ||| @levelIsLevel Proof that `level` is a level
  SuccLevel : (level : Term context) -> .{auto levelIsLevel : HasLevelType level} -> Term context
  ||| The type universe
  ||| @level The universe's level
  ||| @levelIsLevel Proof that `level` is a level
  U : (level : Term context) -> .{auto levelIsLevel : HasLevelType level} -> Term context
  ||| Dependent function type
  ||| @domain The domain of the function
  ||| @domainIsType Proof that the domain is a type
  ||| @range The range of the function, in a new context obtained by adding a variable of the domain's type to the initial context
  ||| @rangeIsType Proof that the range is a type
  Pi : (domain : Term context) ->
       .{auto domainIsType : IsType domain} ->
       (range : Term (Snoc context domain)) ->
       .{auto rangeIsType : IsType range} ->
       Term context
  ||| DeBruijn-indexed variable
  |||
  ||| Free variables can exist in any context, but the typing rules will constrain the index to be valid
  ||| @idx The variable index
  Var : (idx : Nat) -> Term context

||| The term is a type
||| @term The term in question
data IsType : (term : Term context) -> Type where
  ||| Level is a type
  LevelIsType : IsType Level
  ||| The type universe is a type
  UIsType : IsType (U level {levelIsLevel})
  ||| A dependent function type is a type
  PiIsType : IsType (Pi domain {domainIsType} range {rangeIsType})
  ||| `Var Z` is a type in any context whose head is a universe
  VarHeadIsType : IsType (Var Z {context=Snoc context (U level {levelIsLevel}) {typeIsType}})
  ||| If `Var k` is a type in a context, `Var (S k)` is a type in a context with an extra variable
  ||| @predIsType Proof that the predecessor var is a type in the old context
  VarTailIsType : (predIsType : IsType (Var k {context})) -> IsType (Var (S k) {context=Snoc context type {typeIsType}})

||| Proof that a term is a level
||| @term The term in question
data HasLevelType : (term : Term context) -> Type where
  ||| The successor of a level is a level
  SuccLevelHasLevelType : HasLevelType (SuccLevel level {levelIsLevel})
  ||| `Var Z` is a level in any context whose head is the level type
  VarHeadHasLevelType : HasLevelType (Var Z {context=Snoc context Level {typeIsType}})
  ||| If `Var k` is a level in a context, `Var (S k)` is a level in a context with an extra variable
  ||| @predIsType Proof that the predecessor variable's type is a type in the old context
  VarTailHasLevelType : (predIsType : HasLevelType (Var k {context})) -> HasLevelType (Var (S k) {context=Snoc context type {typeIsType}})
 
-- Debugging, shouldn't stick around
instance Show (Term context) where
  show t = show' t False 0 where
    wrapParens : Bool -> String -> String
    wrapParens False s = s
    wrapParens True s = "(" ++ s ++ ")"

    show' : (Term contexxt) -> Bool -> Int -> String
    show' Level _ _ = "Level"
    show' (SuccLevel level) parens varOffset = wrapParens parens ("SuccLevel " ++ (show' level True varOffset))
    show' (U level) parens varOffset = wrapParens parens ("U " ++ (show' level True varOffset))
    show' (Pi domain range) parens varOffset = wrapParens parens ("(" ++ (showVarOffset varOffset) ++ " : " ++ (show' domain True varOffset) ++ ") -> " ++ (show' range False (varOffset + 1))) where
      showVarOffset i = singleton (cast (i + 65))
    show' (Var index) _ varOffset = singleton (cast (varOffset + 64 - (cast index)))
