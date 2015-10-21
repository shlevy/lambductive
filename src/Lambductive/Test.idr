||| Test the calculus
module Lambductive.Test

import Effects
import Effect.StdIO
import Effect.State
import Effect.Exception
import Data.SortedMap

import Lambductive.Core

instance Eq Term where
  U == U = True

instance Ord Term where
  compare U U = EQ

Collection : Type
Collection = List (Term, Maybe String)

printTerm : Term -> Eff () [STDIO]
printTerm U = putStr "\\mathcal{U}"

printTermLookup : Term -> Eff () [STATE (SortedMap Term String), STDIO]
printTermLookup term = do
  case (lookup term !get) of
    Nothing => printTerm term
    Just n => putStr n

printTermTopLevel : Term -> Eff () [STATE (SortedMap Term String), STDIO]
printTermTopLevel term = do
  putStr "("
  printTermLookup term
  putStrLn "\\ Type) \\\\"

printCollection : Collection -> Eff () [STATE (SortedMap Term String), STDIO, EXCEPTION String]
printCollection [] = pure ()
printCollection ((term, Just name) :: tail) = do
  m <- get
  case (lookup term m) of
    Just _ => raise "Duplicate term attempted!"
    Nothing => do
      putStr name
      putStr " \\equiv "
      printTermTopLevel term
      put (insert term name m)
      printCollection tail
printCollection ((term, Nothing) :: tail) = do
  printTermTopLevel term
  printCollection tail

simpleCollection : Collection
simpleCollection = [(U, Nothing), (U, Just "myU"), (U, Nothing)]

instance Default (SortedMap Term String) where
  default = empty

simpleTest : IO ()
simpleTest = do
  run (printCollection simpleCollection)
