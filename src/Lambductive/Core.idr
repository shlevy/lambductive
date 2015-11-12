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

||| Less than relation over levels
data LevelLT : Level -> Level -> Type where
  ||| Any `Smaller` level is less than any `Bigger` level
  LTSmallerBigger : LevelLT (Smaller s) (Bigger b)
  ||| If one Smaller level's distance is less than another's, the second is less than the first
  LTSmaller : LTE (S rhs) lhs -> LevelLT (Smaller lhs) (Smaller rhs)
  ||| If one Bigger level's distance is less than another's, it is less than that other
  LTBigger : LTE (S lhs) rhs -> LevelLT (Bigger lhs) (Bigger rhs)

||| Less than or equal relation over levels
data LevelLTE : Level -> Level -> Type where
  ||| Any `level` is less than or equal to itself
  LTERefl : LevelLTE level level
  ||| If one level is less than another, it is less than or equal to that other
  LTELT : LevelLT level1 level2 -> LevelLTE level1 level2

data Context : Type

data Sort : Type

data Term : Context -> Sort -> Type

data TypeNotU : Term context sort -> Type

||| The sort of a term
|||
||| If terms were parameterized by their types, we would have an infinite descent problem when writing out the type universe itself. Instead, we have separate sorts for memebers of universes and other terms ("Types" and "Values", respectively)
data Sort : Type where
  ||| The term is a type
  |||
  ||| The idris judgment (term : Term context (SortType level)) should be read as the lambductive judgment (context |- term : U level)
  ||| @level The level of the universe the term belongs to
  SortType : (level : Level) -> Sort
  ||| The term is a value (i.e. it is not a type)
  |||
  ||| The idris judgment (term : Term context (SortValue type)) should be read as the lambductive judgment (context |- term : type)
  ||| @type The type of the value
  ||| @ok `type` is not a type universe
  SortValue : (type : Term context (SortType level)) -> .{auto ok : TypeNotU type} -> Sort

||| The variable context of the term
data Context : Type where
  ||| The empty context
  Nil : Context
  ||| Add a variable to an existing context
  ||| @context The existing context
  ||| @type The type of the new variable
  (::) : (context : Context) -> (type : Term context (SortType level)) -> Context

data VarSort : Nat -> Context -> Sort -> Type

||| Terms of the calculus
data Term : Context -> Sort -> Type where
  ||| A type universe
  ||| @level The level of the universe
  ||| @ok `level` is less than the containing universe's level
  U : (level : Level) -> .{auto ok : LevelLT level level'} -> Term context (SortType level')
  ||| A dependent function type
  ||| @domain The domain of the function
  ||| @range The (possibly dependent) range of the function
  Pi : (domain : Term context (SortType level)) ->
       (range : Term (context :: domain) (SortType level)) ->
       Term context (SortType level)
  ||| A variable
  |||
  ||| Note that these are *not* De Bruijn variables!
  ||| @idx The index of the variable from the *end* of its context
  ||| @ok The sort of the variable is valid for the given index and context
  Var : (idx : Nat) -> .{auto ok : VarSort idx context sort} -> Term context sort

||| Calculate the length of a context
length : Context -> Nat
length [] = Z
length (tail :: _) = S (length tail)

||| The valid sort, if any, corresponding to a given variable index and context
|||
||| @idx The variable index
data VarSort : (idx : Nat) -> Context -> Sort -> Type where
  ||| The last variable of a context whose head is a universe is a type of that universe's level or greater
  VarSortLastType : LevelLTE level level' -> VarSort (length context) (context :: (U {ok} level)) (SortType level')
  ||| The last variable of a context whose head is not a universe is a value of that type
  VarSortLastValue : VarSort (length context) (context :: type) (SortValue {ok} type)
  ||| The sort of a given variable index doesn't change when adding a new type to the head of its context
  VarSortCons : VarSort n context sort -> VarSort n (context :: type) sort

||| Types that are not universes
data TypeNotU : Term context sort -> Type where
  ||| Dependent function types are not universes
  PiType : TypeNotU (Pi domain range)
  ||| Variables that are types are not universes
  VarType : TypeNotU (Var idx {ok} {sort=SortType level})

-- Debugging, shouldn't stick around
instance Show (Term context sort) where
  show {context} {sort} term = (showContext context) ++ " |- " ++ (showTerm True term) ++ " : " ++ showSort sort where
    wrapParens : Bool -> String -> String
    wrapParens False s = s
    wrapParens True s = "(" ++ s ++ ")"

    showLevel : Level -> String
    showLevel (Bigger n) = show n
    showLevel (Smaller n) = "-" ++ (show (S n))

    map : ({context : Context} -> {sort : Sort} -> Term context sort -> a) -> Context -> List a
    map f [] = []
    map f (tail :: head) = (f head) :: (map f tail)

    showVar : Nat -> String
    showVar n = singleton (chr ((cast n) + 65))

    showTerm : {sort : Sort} -> {context : Context} -> Bool -> Term context sort -> String
    showTerm parens (U level) = wrapParens parens ("U " ++ (showLevel level))
    showTerm parens (Pi {context} domain range) = wrapParens parens ("(" ++ (showVar (length context)) ++ " : " ++ (showTerm True domain) ++ ") -> " ++ (showTerm False range))
    showTerm _ (Var idx) = showVar idx

    showContext : Context -> String
    showContext c = "[ " ++ (foldr (\s => \acc => s ++ " " ++ acc) "" (map (showTerm False) c)) ++ "]"
    
    showSort : Sort -> String
    showSort (SortType level) = "U " ++ showLevel level
    showSort (SortValue type) = showTerm False type
