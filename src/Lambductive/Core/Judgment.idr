||| Judgments of the calculus
module Lambductive.Core.Judgment

import Lambductive.Core.Term

%default total

||| A judgment of the type of the term
||| @ term The term we're judging
||| @ type The type we're assigning to the term
public
data Judgment : (term : Term) -> (type : Term) -> Type where
  ||| The successor of a level is a level
  ||| @ levelIsLevel A judgment that `level` is a level
  SuccLevelIsLevel : (levelIsLevel : Judgment level Level) -> Judgment (SuccLevel level) Level
  ||| Universes are members of the next universe
  ||| @ levelIsLevel A judgment that `level` is a level
  UIsSuccU : (levelIsLevel : Judgment level Level) -> Judgment (U level) (U (SuccLevel level))
  ||| Members of one universe are members of the next universe
  ||| @ typeIsU A judgment that `type` is a member of some universe
  IsUIsSuccU : (typeIsU : Judgment type (U level)) -> Judgment type (U (SuccLevel level))
