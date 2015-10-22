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
  (UCode n) == (UCode m) = n == m
  (LiftCode n t1) == (LiftCode m t2) = n == m && t1 == t2
  _ == _ = False

instance Ord Term where
  compare (U n) (U m) = compare n m
  compare (UCode n) (UCode m) = compare n m
  compare (LiftCode n t1) (LiftCode m t2) = case (compare n m) of
    EQ => compare t1 t2
    x  => x
  compare (U _) (UCode _) = LT
  compare (U _) (LiftCode _ _) = LT
  compare (UCode _) (LiftCode _ _) = LT
  compare (UCode _) (U _) = GT
  compare (LiftCode _ _) (UCode _) = GT
  compare (LiftCode _ _) (U _) = GT

printTermLookup : Term -> Eff () [STATE (SortedMap Term String), STDIO]

printTerm : Term -> Eff () [STATE (SortedMap Term String), STDIO]
printTerm (U n) = do
  putStr "\\mathcal{U}_{"
  putStr (show n)
  putStr "}"
printTerm (UCode n) = do
  putStr "\\mathcal{u}_{"
  putStr (show n)
  putStr "}"
printTerm (LiftCode n code) = do
  putStr "\\mathsf{Lift}_{"
  putStr (show n)
  putStr "} ("
  printTermLookup code
  putStr ")"

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

uCodeZ : ValidJudgment (UCode Z) (JudgmentValue (U (S Z)))
uCodeZ = UCodeU

universeCodeCollection : Collection
universeCodeCollection = [(MkValid uCodeZ, Nothing)]

public
uCodeTest : IO ()
uCodeTest = run (printCollection universeCodeCollection)

liftCodeCollection : Collection
liftCodeCollection = [(MkValid (LiftCodeU uCodeZ), Nothing)]

public
liftCodeTest : IO ()
liftCodeTest = run (printCollection liftCodeCollection)
