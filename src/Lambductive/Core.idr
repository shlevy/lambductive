||| Lambductive core calculus
module Lambductive.Core

import Data.So

%default total

mutual
  ||| Terms of the calculus
  data Term : Type where
    ||| The type universe
    U : Term
    ||| Dependent function type
    ||| @domain The domain of the function
    ||| @domainType Proof that the domain is a type
    ||| @range The range of the function
    ||| @rangeType Proof that the range is a type
    Pi : (domain : Term) -> .{auto domainType : So (isType domain)} -> (range : Term) -> .{auto rangeType : So (isType range)} -> Term

  ||| Is the term a type?
  ||| @ term The term in question
  isType : (term : Term) -> Bool
  isType U = True
  isType (Pi _ _) = True
