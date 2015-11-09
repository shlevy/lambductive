||| Lambductive core calculus
module Lambductive.Core

%default total

data Context : Type

data Sort : Context -> Type

data Term : (context : Context) -> Sort context -> Type

||| The sort of a term
||| @context The context of the term
data Sort : (context : Context) -> Type where
  ||| The term is a type
  SortType : Sort context
  ||| The term is a value of a given type
  ||| @type The type of the term
  SortValue : (type : Term context SortType) -> Sort context

||| DeBruijn variable context
data Context : Type where
  ||| The empty context
  Nil : Context
  ||| Add a new variable to the context
  ||| @type The type of the new variable
  ||| @context The existing context
  ||| @contextIsSame Proof that the context of `type` is the context we're adding to
  (::) : (type : Term context' SortType) -> (context : Context) -> .{auto contextIsSame : context = context'} -> Context

data ValidUniverseSort : Sort context -> Term context (SortValue type) -> Type

data PiArg : Sort context -> Type

interpretPiArg : Term context sort -> PiArg sort -> Term context SortType

data ValidVarSort : Sort context -> Nat -> Type

liftSort : Sort context -> Sort (type :: context)

||| Terms of the calculus
|||
||| Universe levels are given explicitly, but there is no term for a base level. Instead, terms that reference universes are made level-polymorphic by taking a `Level` as a function argument.
|||
||| Universes are technically à la Tarski (`U {sort=SortType} level` is the type, `U {sort=SortValue (U {sort=SortType} (SuccLevel level))} level` is the code), but we cheat in a few ways:
|||
||| * The difference between the code and the type is all in implicits, which are usually inferred automatically
||| * The second argument to the `Pi` type code has an implicit lambda in front of it. So if we have `f : Pi (A) (U level)`, `Pi {sort=SortValue (U level)} (A) (f (Var 0))` is a pi type code.
||| * If a type code is used in a context where a type is expected, the default implicit logic will infer an implicit `InterpretCode` (but the reverse isn't true, of course!)
||| * The default implicit logic will lift type codes as high as they need to be
||| @context The context of the term
||| @sort The sort of the term
data Term : (context : Context) -> (sort : Sort context) -> Type where
  ||| The type of universe levels
  Level : Term context SortType
  ||| The successor of a level
  ||| @level The level whose successor we're computing
  SuccLevel : (level : Term context (SortValue Level)) -> Term context (SortValue Level)
  ||| The type universe and universe code
  ||| @level The universe's level
  ||| @validUniverseSort Proof that `sort` is a valid sort for a universe of this level
  U : (level : Term context (SortValue Level)) -> .{auto validUniverseSort : ValidUniverseSort sort level} -> Term context sort
  ||| Dependent function type
  ||| @domain The domain of the function
  ||| @domainPiArg Proof that `domain` is a valid argument to `Pi`
  ||| @range The range of the function, in a new context obtained by adding a variable of the domain's type to the initial context
  Pi : (domain : Term context domainSort) ->
       .{auto domainPiArg : PiArg domainSort} ->
       (range : Term ((interpretPiArg domain domainPiArg) :: context) (liftSort domainSort)) ->
       Term context domainSort
  ||| DeBruijn-indexed variable
  ||| @idx The variable index
  ||| @validVarSort Proof that `sort` is a valid sort for a variable with this index in this context
  Var : (idx : Nat) -> .{auto validVarSort : ValidVarSort sort idx} -> Term context sort

data ValidUniverseSort : (Sort context) -> (Term context (SortValue type)) -> Type where
  UIsType : ValidUniverseSort SortType level
  UIsSuccU : ValidUniverseSort (SortValue (U (SuccLevel level) {validUniverseSort=UIsType})) level
  LiftUIsU : ValidUniverseSort (SortValue (U level1 {validUniverseSort})) level -> ValidUniverseSort (SortValue (U (SuccLevel level1) {validUniverseSort=UIsType})) level 

data PiArg : (sort : Sort context) -> Type where
  TypePiArg : PiArg SortType
  UPiArg : PiArg (SortValue (U level))

drop : Nat -> Context -> Context
drop _ [] = []
drop Z context = context
drop (S k) (_ :: tail) = drop k tail

dropZNeutral : (context : Context) -> context = drop Z context
dropZNeutral [] = Refl
dropZNeutral (_ :: _) = Refl

insertAt : (offset : Nat) -> (context : Context) -> Term (drop offset context) SortType -> Context
insertAt _ [] type = type :: []
insertAt Z context type = (::) type context {contextIsSame=dropZNeutral context}
insertAt (S k) (_ :: tail) type = insertAt k tail type

lift : Term context SortType -> (offset : Nat) -> Term (insertAt offset context type) SortType
lift offset term = ?hole
{-
data ValidVarSort : (Sort context) -> Nat -> Type where
  VarZIsHead : ValidVarSort (SortValue {context=head :: tail} (lift Z head)) Z
  VarSIsPred : ValidVarSort sort k -> ValidVarSort (liftSort sort) (S k)
  LiftVarIsU : ValidVarSort (SortValue (U level)) n -> ValidVarSort (SortValue (U (SuccLevel level))) n
  InterpretVarIsType : ValidVarSort (SortValue (U level)) n -> ValidVarSort SortType n

liftSort SortType = SortType
liftSort (SortValue type) = SortValue (lift type Z)

lift Level _ = Level
lift (SuccLevel level) offset = SuccLevel (lift level offset)
lift (U level) offset = U (lift level offset)
lift (Pi domain range) offset = Pi (lift domain offset) (lift range (S offset))
lift (Var idx) offset = Var (if offset <= idx then S idx else idx)

interpretPiArg type TypePiArg = type
interpretPiArg (U level) UPiArg = U level
interpretPiArg (Pi domain {domainPiArg} range) UPiArg = Pi (interpretPiArg domain domainPiArg) range
interpretPiArg (Var idx) UPiArg = Var idx
 
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
-}
