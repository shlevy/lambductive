||| The lambductive core calculus
module Lambductive

mutual
  ||| Terms of the language
  public data Term : Type where
    ||| The base (tarski-style) universe
    U : Term
    ||| The universe interpretation operator
    El : (HasType {type = U} term u) -> Term

  ||| The term is a type
  public data IsType : Term -> Type where
    ||| The universe is a type
    UIsType  : IsType U
    ||| The result of the universe interpretation operator is a type
    ElIsType : IsType (El code)

  ||| The term has the given type
  public data HasType : Term -> (IsType type) -> Type where
