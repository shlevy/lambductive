||| The lambductive core calculus
module Lambductive

%default total

mutual
  ||| Judgment context
  public data Context : Type where
    ||| The empty context
    Empty  : Context
    ||| Create a new context with the head variable having a given type
    Snoc : (ctx : Context) -> IsType ctx type -> Context

  ||| Terms of the language
  public data Term : Type where
    ||| The base (tarski-style) universe
    U : Term
    ||| The universe interpretation operator
    El : (HasType {ctx = ctx} {type = U} term u) -> Term
    ||| The pi type former
    Pi : (A : IsType ctx a) -> IsType (Snoc ctx A) b -> Term
    ||| A variable
    ||| @ idx the de Bruijn index
    Var : (idx : Nat) -> Term

  ||| The term is a type in the context
  public data IsType : Context -> Term -> Type where
    ||| |_ U Type
    UIsType : IsType ctx U
    ||| |_ |- code : U -> |_ El(code) Type
    ElIsType : IsType ctx (El {ctx = ctx} code)
    ||| |_ A Type, |_ B Type -> Pi(A, B) Type
    PiIsType : IsType ctx (Pi {ctx = ctx} a b)
    ||| |_ |- A Type -> (|_, B) |- (succ A) type
    SuccIsType : IsType ctx a -> IsType (Snoc ctx b) (succ a)

  ||| The term has the given type in the context
  public data HasType : Term -> (IsType ctx type) -> Type where
    ||| The head variable has the type of the head of the context
    HeadVarHasType : HasType (Var 0) (SuccIsType {b = type} type)
    ||| |_ |- a : A -> (|_, B) |- succ (a) : succ (B)
    SuccHasType : HasType term type -> HasType (succ term) (SuccIsType type)

  ||| Bump the variable indices of a term in a way that preserves judgments
  public
  succ : Term -> Term
  succ U = U
  succ (El typecheck) = El (SuccHasType typecheck)
  succ (Pi a b) = Pi (SuccIsType a) (SuccIsType b)
  succ (Var idx) = Var (S idx)
