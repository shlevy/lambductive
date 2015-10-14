||| The lambductive core calculus
module Lambductive

%default total

data Context : Nat -> Type

data TypeTerm : Context n -> Type

||| Term context, with de Bruijn indexed variables
||| @ n The number of variables
public data Context : (n : Nat) -> Type where
  ||| []
  Empty : Context Z
  ||| (a : A) :: Γ
  ||| @ ctx The initial context
  ||| @ type The type of the new variable
  Snoc : (ctx : Context n) -> (type : TypeTerm ctx) -> Context (S n)

||| Drop variables from a context
||| @ n The number of variables to drop
public
drop : (n : Nat) -> Context (n + m) -> Context m
drop Z ctx = ctx
drop (S k) (Snoc ctx _) = drop k ctx

||| Insert a variable into a context
||| @ n The offset to insert the variable at
||| @ ctx The context to insert into
||| @ type The type of the new variable
public
insertAt : (n : Nat) -> (ctx : Context (n + m)) -> (type : TypeTerm (drop n ctx)) -> Context (S (n + m))

data ValueTerm : TypeTerm ctx -> Type

||| Γ |- X Type
||| @ ctx The context in which the term is a type
public data TypeTerm : (ctx : Context n) -> Type where
  ||| Γ |- A Type -> (insertAt n Γ B) |- (SuccType A) Type
  ||| @ type The type to lift into the new context
  SuccType : (type : TypeTerm ctx) -> TypeTerm (insertAt {m = m} n ctx type2)
  ||| Γ |- U Type
  U : TypeTerm ctx
  ||| Γ |- code : U -> Γ |- (Interpret code) Type
  ||| @ code The type code to interpret
  Interpret : (code : ValueTerm {ctx = ctx} U) -> TypeTerm ctx
  ||| Γ |- A Type -> (a : A) :: Γ |- B Type -> Γ |- Pi A B Type
  Pi : (A : TypeTerm ctx) -> TypeTerm (Snoc ctx A) -> TypeTerm ctx

insertAt Z ctx type = Snoc ctx type
insertAt (S k) (Snoc ctx head) type = Snoc (insertAt k ctx type) (SuccType head)

||| Extract a variable from a context
||| @ n The variable index
||| @ ctx The context
public
index : (n : Nat) -> (ctx : Context (S (n + m))) -> TypeTerm ctx
index Z (Snoc _ type) = SuccType {n = Z} type
index (S k) (Snoc ctx _) = SuccType {n = Z} (index k ctx)

data TypeEquivalence : TypeTerm ctx -> TypeTerm ctx -> Type

||| Γ |- X type -> Γ |- (x : X)
||| @ type The type of the value
public data ValueTerm : (type : TypeTerm ctx) -> Type where
  ||| Γ |- a : A -> (insertAt n Γ B) |- (SuccValue a) : (SuccType A)
  ||| @ value The value to lift into the new context
  SuccValue : (value: ValueTerm type) -> ValueTerm (SuccType type)
  ||| Γ |- A = B Type -> Γ |- a : A -> Γ |- a : B
  ||| @ prf The proof of equivalence
  ||| @ value The value whose type we want to transport
  TransportType : (prf : TypeEquivalence type1 type2) -> (value : ValueTerm type1) -> ValueTerm type2
  ||| Γ |- (Var idx) : (index idx Γ)
  ||| @ idx The de Bruijn index to look up
  Var : (idx : Nat) -> ValueTerm (index idx ctx)

||| insertAt (n + 1) ((a : A) :: Γ) B = (a : SuccType A) :: (insertAt n Γ B)
insertAtPiLemma : insertAt (S n) (Snoc ctx a) type = Snoc (insertAt n ctx type) (SuccType a)
insertAtPiLemma = Refl

||| Γ |- A Type -> Γ |- B Type -> Γ |- A = B Type
||| @ type1 The LHS type
||| @ type2 The RHS type
public data TypeEquivalence : (type1 : TypeTerm ctx) -> (type2 : TypeTerm ctx) -> Type where
  ||| Γ |- A = A Type
  TypeEquivalenceRefl : TypeEquivalence a a
  ||| Γ |- A = B Type -> Γ |- B = A Type
  ||| @ prf The proof of equivalence
  TypeEquivalenceSym : (prf : TypeEquivalence a b) -> TypeEquivalence b a
  ||| Γ |- A = B Type -> Γ |- B = C Type -> Γ |- A = C Type
  ||| @ proof1 The first proof of equivalence
  ||| @ proof2 The second proof of equivalence
  TypeEquivalenceTrans : (proof1 : TypeEquivalence a b) -> (proof2 : TypeEquivalence b c) -> TypeEquivalence a c
  ||| Γ |- SuccType U = U Type
  SuccU : TypeEquivalence (SuccType U) U
  ||| Γ |- SuccType (Interpret code) = Interpret (SuccValue code) Type
  SuccInterpret : TypeEquivalence (SuccType (Interpret code)) (Interpret (TransportType SuccU (SuccValue code)))
  ||| Γ |- SuccType (Pi A B) = Pi (SuccType A) (SuccType B)
  SuccPi : TypeEquivalence (SuccType (Pi a b)) (Pi (SuccType {n = n} {m = m} a) (replace (insertAtPiLemma {a = a}) (SuccType {n = S n} {m = m} b)))
