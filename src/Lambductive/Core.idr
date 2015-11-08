||| Lambductive core calculus
module Lambductive.Core

%default total

||| Judgment of whether a term is a type
data IsTypeJudgment : Type where
  ||| The term is a type
  IsType    : IsTypeJudgment
  ||| The term is not a type
  IsNotType : IsTypeJudgment

data Context : Type

data Term : IsTypeJudgment -> Context -> Type

||| DeBruijn variable context
data Context : Type where
  ||| The empty context
  Nil : Context
  ||| Add a new variable to the context
  ||| @context The existing context
  ||| @type The type of the new variable
  Snoc : (context : Context) -> (type : Term IsType context) -> Context

data HasLevelType : Term isType context -> Type

||| Whether a variable is a type in a given context
||| @idx The index of the variable
||| @context The context of the variable
varIsType : (idx : Nat) -> (context : Context) -> IsTypeJudgment

||| Terms of the calculus
||| @isType Whether the term is a type
||| @context The context of the term
data Term : (isType : IsTypeJudgment) -> (context : Context) -> Type where
  ||| The type of universe levels
  Level : Term IsType context
  ||| The successor of a level
  ||| @level The level whose successor we're computing
  ||| @levelIsLevel Proof that `level` is a level
  SuccLevel : (level : Term isType context) -> .{auto levelIsLevel : HasLevelType level} -> Term IsNotType context
  ||| The type universe
  ||| @level The universe's level
  ||| @levelIsLevel Proof that `level` is a level
  U : (level : Term isType context) -> .{auto levelIsLevel : HasLevelType level} -> Term IsType context
  ||| Dependent function type
  ||| @domain The domain of the function
  ||| @range The range of the function, in a new context obtained by adding a variable of the domain's type to the initial context
  Pi : (domain : Term IsType context) ->
       (range : Term IsType (Snoc context domain)) ->
       Term IsType context
  ||| DeBruijn-indexed variable
  |||
  ||| Free variables can exist in any context, but the typing rules will constrain the index to be valid when bound
  ||| @idx The variable index
  Var : (idx : Nat) -> Term (varIsType idx context) context

varIsType Z (Snoc _ (U _)) = IsType
varIsType (S k) (Snoc ctx _) = varIsType k ctx
varIsType _ _ = IsNotType

||| Proof that a term is a level
||| @term The term in question
data HasLevelType : (term : Term isType context) -> Type where
  ||| The successor of a level is a level
  SuccLevelHasLevelType : HasLevelType (SuccLevel level {levelIsLevel})
  ||| `Var Z` is a level in any context whose head is the level type
  VarHeadHasLevelType : HasLevelType (Var Z {context=Snoc context Level})
  ||| If `Var k` is a level in a context, `Var (S k)` is a level in a context with an extra variable
  ||| @predIsLevel Proof that the predecessor variable is a level
  VarTailHasLevelType : (predIsLevel : HasLevelType (Var k {context})) -> HasLevelType (Var (S k) {context=Snoc context type})
 
-- Debugging, shouldn't stick around
instance Show (Term isType context) where
  show t = show' t False 0 where
    wrapParens : Bool -> String -> String
    wrapParens False s = s
    wrapParens True s = "(" ++ s ++ ")"

    show' : (Term isType context) -> Bool -> Int -> String
    show' Level _ _ = "Level"
    show' (SuccLevel level) parens varOffset = wrapParens parens ("SuccLevel " ++ (show' level True varOffset))
    show' (U level) parens varOffset = wrapParens parens ("U " ++ (show' level True varOffset))
    show' (Pi domain range) parens varOffset = wrapParens parens ("(" ++ (showVarOffset varOffset) ++ " : " ++ (show' domain True varOffset) ++ ") -> " ++ (show' range False (varOffset + 1))) where
      showVarOffset i = singleton (cast (i + 65))
    show' (Var index) _ varOffset = singleton (cast (varOffset + 64 - (cast index)))
