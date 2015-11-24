||| Lambductive core calculus
module Lambductive.Core

%default total

data Context : Type

data TypeTerm : Context -> Type

infixl 7 :::

||| De Bruijn variable context
data Context : Type where
  Nil : Context
  ||| Add a variable to a context
  ||| @type The type of the variable
  (:::) : (context : Context) -> (type : TypeTerm context) -> Context

||| Judgment of whether the interpretation of a term as a type code is reducible
data InterpretReducibility : Type where
  InterpretReducible : InterpretReducibility
  InterpretIrreducible : InterpretReducibility

data ValueTerm : (context : Context) -> TypeTerm context -> InterpretReducibility -> Type

||| Types of the calculus
data TypeTerm : Context -> Type where
  ||| A universe of type codes
  U : (level : Nat) -> TypeTerm context
  ||| Dependent function type
  Pi : (domain : TypeTerm context) -> (codomain : TypeTerm (context ::: domain)) -> TypeTerm context
  ||| An irreducible application of the type code interpretation operator
  |||
  ||| Use the `interpret` function to interpret type codes without any concern for reducibility
  IrreducibleInterpret : ValueTerm context (U level) InterpretIrreducible -> TypeTerm context

||| Bring a type into a context with an extra variable at the head
addVarToType : TypeTerm context -> TypeTerm (context ::: type)

||| An index into a context
||| @type The type of the variable at that index
data ContextIndex : (context : Context) -> (type : TypeTerm context) -> Type where
  Z : ContextIndex (_ ::: type) (addVarToType type)
  S : ContextIndex context type -> ContextIndex (context ::: type') (addVarToType type)

||| Interpret a type code to a type
interpret : ValueTerm context (U _) _ -> TypeTerm context

||| Values of the calculus
data ValueTerm : (context : Context) -> TypeTerm context -> InterpretReducibility -> Type where
  Var : ContextIndex context type -> ValueTerm context type InterpretIrreducible

interpret (Var idx) = IrreducibleInterpret (Var idx)

||| An offset into a context
data ContextOffset : Context -> Type where
  OffZ : ContextOffset context
  OffS : ContextOffset context -> ContextOffset (context ::: type)

||| Drop some variables from a context
drop : (context : Context) -> ContextOffset context -> Context
drop context OffZ = context
drop (context ::: _) (OffS off) = drop context off

||| Insert a variable into a context at a given offset
||| @type The type of the variable
insertAt : (context : Context) -> (off : ContextOffset context) -> (type : TypeTerm (drop context off)) -> Context

||| Bring a type into a context with an extra variable at a given offset
addVarToTypeAtOffset : (off : ContextOffset context) -> TypeTerm context -> TypeTerm (insertAt context off type)

insertAt context OffZ type = context ::: type
insertAt (context ::: type) (OffS off) type' = insertAt context off type' ::: addVarToTypeAtOffset off type

||| Bring a type code into a context with an extra variable at a given offset
addVarToCodeAtOffset : (off : ContextOffset context) -> ValueTerm context (U level) interpretReducible -> ValueTerm (insertAt context off type') (U level) interpretReducible

addVarToTypeAtOffset _ (U level) = U level
addVarToTypeAtOffset off (Pi domain codomain) = Pi (addVarToTypeAtOffset off domain) (addVarToTypeAtOffset (OffS off) codomain)
addVarToTypeAtOffset off (IrreducibleInterpret code) = IrreducibleInterpret (addVarToCodeAtOffset off code)

addVarToType type = addVarToTypeAtOffset OffZ type

||| Bring a value into a context with an extra variable at a given offset
addVarToValueAtOffset : (off : ContextOffset context) -> ValueTerm context type interpretReducible -> ValueTerm (insertAt context off type') (addVarToTypeAtOffset off type) interpretReducible
addVarToValueAtOffset OffZ (Var idx) = Var (S idx)
addVarToValueAtOffset (OffS off) (Var idx) = ?hole

addVarToCodeAtOffset off code = addVarToValueAtOffset off code
