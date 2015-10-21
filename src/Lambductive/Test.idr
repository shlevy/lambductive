||| Test the calculus
module Lambductive.Test

import Effects
import Effect.StdIO
import Effect.State
import Effect.Exception
import Data.SortedMap

import Lambductive.Core

instance Eq Term where
  (U _) == (U _) = True

instance Ord Term where
  compare (U _) (U _) = EQ

printTerm : Term -> Eff () [STDIO]
printTerm (U _) = putStr "\\mathcal{U}"

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

simpleCollection : Collection
simpleCollection = [(MkValid (UType {level=Z}), Nothing), (MkValid (UType {level=Z}), Just "myU"), (MkValid (UType {level=Z}), Nothing)]

instance Default (SortedMap Term String) where
  default = empty

public
simpleTest : IO ()
simpleTest = do
  run (printCollection simpleCollection)
