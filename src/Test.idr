||| A module for testing the system.
|||
||| Since this is a library for defining valid constructions, we only need to typecheck this to test.
module Test

import Lambductive

||| |- U type
universeIsAType : IsType Empty U
universeIsAType = UIsType

||| code : U |- El(code) type
interpretedUniverseElementIsAType : (code: HasType {ctx = Empty} {type = U} x u) -> IsType Empty (El code)
interpretedUniverseElementIsAType code = ElIsType {code = code}

||| A Type |- B Type -> Pi(A, B) type
piFormsAType : (A : IsType Empty a) -> (B: IsType (Snoc Empty A) b) -> IsType Empty (Pi A B)
piFormsAType A B = PiIsType {a = A} {b = B}
