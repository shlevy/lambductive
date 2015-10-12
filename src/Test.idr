||| A module for testing the system.
|||
||| Since this is a library for defining valid constructions, we only need to typecheck this to test.
module Test

import Lambductive

||| |- U type
universeIsAType : IsType Nil U
universeIsAType = UIsType

||| code : U |- El(code) type
interpretedUniverseElementIsAType : (code: HasType {ctx = Nil} {type = U} x u) -> IsType Nil (El code)
interpretedUniverseElementIsAType code = ElIsType {code = code}

||| A Type, B Type -> Pi(A, B) type
piFormsAType : (A : IsType Nil a) -> (B: IsType Nil b) -> IsType Nil (Pi A B)
piFormsAType A B = PiIsType {a = A} {b = B}
