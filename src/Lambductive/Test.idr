||| Test the calculus
module Lambductive.Test

import Effects
import Effect.StdIO
import Effect.State
import Effect.Exception
import Data.SortedMap

import Lambductive.Core

%default total

instance Eq Term where
  (U n) == (U m) = n == m
  (Axiom name1) == (Axiom name2) = name1 == name2
  (UCode n) == (UCode m) = n == m
  _ == _ = False

instance Ord Term where
  compare (U n) (U m) = compare n m
  compare (Axiom name1) (Axiom name2) = compare name1 name2
  compare (UCode n) (UCode m) = compare n m
  compare (Axiom _) (U _) = LT
  compare (Axiom _) (UCode _) = LT
  compare (U _) (UCode _) = LT
  compare (U _) (Axiom _) = GT
  compare (UCode _) (Axiom _) = GT
  compare (UCode _) (U _) = GT

printTerm : Term -> Eff () [STDIO]
printTerm (U n) = do
  putStr "\\mathcal{U}_{"
  putStr (show n)
  putStr "}"
printTerm (UCode n) = do
  putStr "\\mathcal{u}_{"
  putStr (show n)
  putStr "}"
printTerm (Axiom name) = do
  putStr "\\mathbf{"
  putStr name
  putStr "}"

printTermLookup : Term -> Eff () [STATE (SortedMap Term String), STDIO]
printTermLookup term = do
  case (lookup term !get) of
    Nothing => printTerm term
    Just n => do
      putStr "\\mathsf{"
      putStr n
      putStr "}"

data Valid : Type where
  MkValid : {term : Term} -> {judgment : Judgment} -> ValidJudgment term judgment -> Valid

Collection : Type
Collection = List (Valid, Maybe String)

printTermTopLevel : Valid -> Eff () [STATE (SortedMap Term String), STDIO]
printTermTopLevel (MkValid {judgment} {term} _) = do
  printTermLookup term
  case judgment of
    JudgmentType => putStrLn "\\ \\mathsf{Type} \\\\"
    JudgmentValue type => do
      putStr "\\ :\\ "
      printTerm type
      putStrLn " \\\\"

printCollection : Collection -> Eff () [STATE (SortedMap Term String), STDIO, EXCEPTION String]
printCollection [] = pure ()
printCollection ((MkValid {term} prf, Just name) :: tail) = do
  m <- get
  case (lookup term m) of
    Just _ => raise "Duplicate term attempted!"
    Nothing => do
      putStr "\\mathsf{"
      putStr name
      putStr "} \\equiv "
      printTermTopLevel (MkValid prf)
      put (insert term name m)
      printCollection tail
printCollection ((term, Nothing) :: tail) = do
  printTermTopLevel term
  printCollection tail

universeCollection : Collection
universeCollection = [(MkValid (UType {level=Z}), Nothing), (MkValid (UType {level=Z}), Just "myU"), (MkValid (UType {level=Z}), Nothing)]

instance Default (SortedMap Term String) where
  default = empty

public
universeTest : IO ()
universeTest = run (printCollection universeCollection)

fooAxiomType : ValidJudgment (Axiom "Foo") JudgmentType
fooAxiomType = AxiomAny

fooAxiomValue : ValidJudgment (Axiom "foo") (JudgmentValue (Axiom "Foo"))
fooAxiomValue = AxiomAny

axiomCollection : Collection
axiomCollection = [(MkValid fooAxiomType, Nothing), (MkValid fooAxiomValue, Nothing)]

public
axiomTest : IO ()
axiomTest = run (printCollection axiomCollection)

uCodeZ : ValidJudgment (UCode Z) (JudgmentValue (U (S Z)))
uCodeZ = UCodeU

universeCodeCollection : Collection
universeCodeCollection = [(MkValid uCodeZ, Nothing)]

public
uCodeTest : IO ()
uCodeTest = run (printCollection universeCodeCollection)
