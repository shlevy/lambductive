||| A module for testing the system.
|||
||| Since this is a library for defining valid constructions, we only need to typecheck this to test.
module Test

import Lambductive

||| The base universe is a type
universeIsAType : IsType U
universeIsAType = UIsType

||| Given an element of the base universe, we can interpret it as a type
interpretedUniverseElementIsAType : (code: HasType {type = U} x u) -> IsType (El code)
interpretedUniverseElementIsAType code = ElIsType {code = code}
