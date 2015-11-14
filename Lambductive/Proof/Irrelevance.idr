||| Proofs of the computational irrelevance of certain proof terms
module Lambductive.Proof.Irrelevance

import Lambductive.Core

%default total

inContextBoundsIrrelevant : (a : InContextBounds idx context) -> (b : InContextBounds idx context) -> a = b
inContextBoundsIrrelevant InBoundsZ InBoundsZ = Refl
inContextBoundsIrrelevant (InBoundsS a) (InBoundsS b) with (inContextBoundsIrrelevant a b)
  inContextBoundsIrrelevant (InBoundsS a) (InBoundsS a) | Refl = Refl
