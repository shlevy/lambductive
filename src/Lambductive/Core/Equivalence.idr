||| Equivalences between terms
module Lambductive.Core.Equivalence

import Lambductive.Core.Term

%default total

||| An equivalence between terms
||| @ lhs The left hand side of the equivalence
||| @ rhs The right hand side of the equivalence
public
data Equivalence : (lhs : Term) -> (rhs : Term) -> Type where
