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

Collection : Type
Collection = List (Term, Maybe String)

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

printTermTopLevel : Term -> Eff () [STATE (SortedMap Term String), STDIO]
printTermTopLevel term = do
  printTermLookup term
  putStrLn "\\ \\mathsf{Type} \\\\"

printCollection : Collection -> Eff () [STATE (SortedMap Term String), STDIO, EXCEPTION String]
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
simpleCollection = [(U Z, Nothing), (U Z, Just "myU"), (U Z, Nothing)]

instance Default (SortedMap Term String) where
  default = empty

simpleTest : IO ()
simpleTest = do
  run (printCollection simpleCollection)