||| The lambductive core calculus
module Lambductive

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

  ||| The term is a type in the context
  public data IsType : Context -> Term -> Type where
    ||| |_ U Type
    UIsType : IsType ctx U
    ||| |_ |- code : U -> |_ El(code) Type
    ElIsType : IsType ctx (El {ctx = ctx} code)
    ||| |_ A Type, |_ B Type -> Pi(A, B) Type
    PiIsType : IsType ctx (Pi {ctx = ctx} a b)

  ||| The term has the given type in the context
  public data HasType : Term -> (IsType ctx type) -> Type where
