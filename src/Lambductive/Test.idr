||| Test the calculus
module Lambductive.Test

import Effects
import Effect.StdIO
import Effect.State
import Effect.Exception
import Data.SortedMap

import Lambductive.Core

data WellFormedTerm : Type where
  MkWellFormedTerm : WellFormed term -> WellFormedTerm

instance Eq WellFormedTerm where
  (MkWellFormedTerm UType) == (MkWellFormedTerm UType) = True

instance Ord WellFormedTerm where
  compare (MkWellFormedTerm UType) (MkWellFormedTerm UType) = EQ

Collection : Type
Collection = List (WellFormedTerm, Maybe String)

printTerm : WellFormedTerm -> Eff () [STDIO]
printTerm (MkWellFormedTerm UType) = putStr "\\mathcal{U}"

printTermLookup : WellFormedTerm -> Eff () [STATE (SortedMap WellFormedTerm String), STDIO]
printTermLookup term = do
  case (lookup term !get) of
    Nothing => printTerm term
    Just n => do
      putStr "\\mathsf{"
      putStr n
      putStr "}"

printTermTopLevel : WellFormedTerm -> Eff () [STATE (SortedMap WellFormedTerm String), STDIO]
printTermTopLevel term = do
  printTermLookup term
  putStrLn "\\ \\mathsf{Type} \\\\"

printCollection : Collection -> Eff () [STATE (SortedMap WellFormedTerm String), STDIO, EXCEPTION String]
printCollection [] = pure ()
printCollection ((term, Just name) :: tail) = do
  m <- get
  case (lookup term m) of
    Just _ => raise "Duplicate term attempted!"
    Nothing => do
      putStr "\\mathsf{"
      putStr name
      putStr "} \\equiv "
      printTermTopLevel term
      put (insert term name m)
      printCollection tail
printCollection ((term, Nothing) :: tail) = do
  printTermTopLevel term
  printCollection tail

simpleCollection : Collection
simpleCollection = [(MkWellFormedTerm (UType {level=Z}), Nothing), (MkWellFormedTerm (UType {level=Z}), Just "myU"), (MkWellFormedTerm (UType {level=Z}), Nothing)]

instance Default (SortedMap WellFormedTerm String) where
  default = empty

public
simpleTest : IO ()
simpleTest = do
  run (printCollection simpleCollection)
