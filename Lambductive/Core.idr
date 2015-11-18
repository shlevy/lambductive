||| Lambductive core calculus
module Lambductive.Core

%default total

data Context : Type

data UniverseJudgment : Type where
  IsUniverse : (level : Nat) -> UniverseJudgment
  NotUniverse : UniverseJudgment

data TypeJudgment : Context -> Type

data Term : (context : Context) -> TypeJudgment context -> UniverseJudgment -> Type

data TypeJudgment : (context : Context) -> Type where
  ||| The term is a type
  ||| @level The level of the universe it belongs to
  IsType : (level : Nat) -> TypeJudgment context
  ||| The term is not a type
  ||| @type The type of the term
  HasType : (type : Term context (IsType _) NotUniverse) -> TypeJudgment context

infixl 7 :::

||| Variable context of terms
data Context : Type where
  Nil : Context
  ||| Add a variable to a context
  ||| @type The type of the new variable
  (:::) : (context : Context) -> (type : Term context (IsType _) _) -> Context

||| The type judgment corresponding to the given type
typeJudgment : Term context (IsType _) isUniverse -> TypeJudgment context
typeJudgment _ {isUniverse=IsUniverse level} = IsType level
typeJudgment type {isUniverse=NotUniverse} = HasType type

addVarToTypeJudgment : TypeJudgment context -> TypeJudgment (context ::: type)

||| A De Bruijn index into a context
||| @judgment The type judgment that applies to variables of this index
data ContextIndex : (context : Context) -> (judgment : TypeJudgment context) -> Type where
  Z : ContextIndex (_ ::: type) (addVarToTypeJudgment (typeJudgment type))
  S : ContextIndex context judgment -> ContextIndex (context ::: type) (addVarToTypeJudgment judgment)

||| The maximum of two naturals, without using the Ord instance
max : Nat -> Nat -> Nat
max Z n = n
max (S n) Z = S n
max (S n) (S m) = S (max n m)

data Term : (context : Context) -> TypeJudgment context -> UniverseJudgment -> Type where
  U : (level : Nat) -> Term context (IsType (S level)) (IsUniverse level)
  Pi : (domain : Term context (IsType level1) _) -> (codomain : Term (context ::: domain) (IsType level2) _) -> Term context (IsType (max level1 level2)) NotUniverse
  Var : ContextIndex context type -> Term context type NotUniverse

||| An offset into a context
data ContextOffset : Context -> Type where
  OffZ : ContextOffset context
  OffS : ContextOffset context -> ContextOffset (context ::: _)

drop : (context : Context) -> ContextOffset context -> Context
drop context OffZ = context
drop (context ::: _) (OffS off) = drop context off

||| Insert a variable at an offset into a context
insertAt : (context : Context) -> (offset : ContextOffset context) -> Term (drop context offset) (IsType _) _ -> Context

addVarToTypeAtOffset : (offset : ContextOffset context) ->
                       Term context (IsType level) universeJudgment ->
                       (type : Term (drop context offset) (IsType _) _) ->
                       Term (insertAt context offset type) (IsType level) universeJudgment

insertAt context OffZ type = context ::: type
insertAt (context ::: head) (OffS n) type = (insertAt context n type) ::: addVarToTypeAtOffset n head type

addVarToTypeJudgment (IsType level) = IsType level
addVarToTypeJudgment (HasType type) {type=type'} = HasType (addVarToTypeAtOffset OffZ type type')

addVarToTypeAtOffset _ (U level) _ = U level
addVarToTypeAtOffset n (Pi domain codomain) type = Pi (addVarToTypeAtOffset n domain type) (addVarToTypeAtOffset (OffS n) codomain type)
addVarToTypeAtOffset n (Var idx) type = Var (addVarToTypeContextIndex n idx type) where
  caseIdx : (o : ContextOffset c) ->
            (i : ContextIndex (c ::: t') j) ->
            (t : Term (drop c o) (IsType _) _) ->
            j = IsType l ->
            ContextIndex (insertAt c o t ::: addVarToTypeAtOffset o t' t) (IsType l)

  addVarToTypeContextIndex : (o : ContextOffset c) ->
                             (i : ContextIndex c (IsType l)) ->
                             (t : Term (drop c o) (IsType l') _) ->
                             ContextIndex (insertAt c o t) (IsType l)
  addVarToTypeContextIndex OffZ i t = S i
  addVarToTypeContextIndex (OffS o) i t = caseIdx o i t Refl

  injectivityLemma : addVarToTypeJudgment j = IsType l -> j = IsType l
  injectivityLemma {j=IsType l} Refl = Refl

  caseIdx _ Z _ {t' = U _} Refl = Z
  caseIdx o (S n) t p = S (addVarToTypeContextIndex o (replace (injectivityLemma p) n) t)
