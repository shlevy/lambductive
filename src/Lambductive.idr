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

data ValueTerm : TypeTerm ctx -> Type

||| Γ |- X Type
||| @ ctx The context in which the term is a type
public data TypeTerm : (ctx : Context n) -> Type where
  ||| Γ |- U Type
  U : TypeTerm ctx
  ||| Γ |- code : U -> Γ |- (Interpret code) Type
  ||| @ code The type code to interpret
  Interpret : (code : ValueTerm {ctx} U) -> TypeTerm ctx
  ||| Γ |- A Type -> (a : A) :: Γ |- B Type -> Γ |- Pi A B Type
  Pi : (A : TypeTerm ctx) -> TypeTerm (Snoc ctx A) -> TypeTerm ctx

||| Insert a variable into a context
||| @ n The offset to insert the variable at
||| @ ctx The context to insert into
||| @ type The type of the new variable
public
insertAt : (n : Nat) -> (ctx : Context (n + m)) -> (type : TypeTerm (drop n ctx)) -> Context (S (n + m))

||| Γ |- A Type -> (insertAt n Γ B) |- (succType A) Type
||| @ idx The index of the new variable in the new context
||| @ type The type to lift into the new context
public
succType : (idx : Nat) -> (type : TypeTerm ctx) -> TypeTerm (insertAt idx ctx newType)

||| Γ |- a : A -> (insertAt n Γ B) |- (succValue a) : (succType A)
||| @ idx The index of the new variable in the new context
||| @ value The value to lift into the new context
public
succValue : (idx : Nat) -> {ctx : Context (idx + m)} -> {type : TypeTerm ctx} -> (value : ValueTerm type) -> ValueTerm (succType idx type)

insertAt Z ctx type = Snoc ctx type
insertAt (S k) (Snoc ctx head) type = Snoc (insertAt k ctx type) (assert_total (succType k head))

succUIsU : succType n U = U

succType n U = U
succType n (Interpret code) = Interpret (assert_total (replace succUIsU (succValue n code)))
succType n (Pi a b) = Pi (succType n a) (succType (S n) b)

succUIsU = Refl

||| Extract a variable from a context
||| @ n The variable index
||| @ ctx The context
public
index : (n : Nat) -> (ctx : Context (S (n + m))) -> TypeTerm ctx
index Z (Snoc _ type) = succType Z type
index (S k) (Snoc ctx _) = succType Z (index k ctx)

||| Γ |- X type -> Γ |- (x : X)
||| @ type The type of the value
public data ValueTerm : {ctx : Context n} -> (type : TypeTerm ctx) -> Type where
  ||| Γ |- (Var idx) : (index idx Γ)
  ||| @ idx The de Bruijn index to look up
  Var : (idx : Nat) -> ValueTerm (index idx ctx)

succValue n {m} with (plus n m)
  | _ = ?hole

{-
data SuccValueView : Nat -> ValueTerm type -> Type where
  SuccValueViewS : {ctx : Context (S (plus idx m))} -> SuccValueView (S (plus idx m)) (Var {ctx} idx)

succValueView : {sum : Nat} -> {ctx : Context sum} -> {type : TypeTerm ctx} -> (v: ValueTerm type) -> SuccValueView sum v
succValueView (Var idx) = SuccValueViewS

succValue n {m} {ctx} v with (plus n m)
  | sum with (succValueView v)
    succValue n {m} (Var idx) | (S (plus idx _)) | SuccValueViewS = ?hole
-}
