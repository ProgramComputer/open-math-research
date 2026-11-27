import LinearSlabs

open OpenMathResearch.LongCycleExcedances

-- The inequality proof does not depend on executable evaluation.
#eval do
  for j in List.finRange 9 do
    let values := (List.range 241).map (linearSlabTable j)
    IO.println (toString (linearSlabX j) ++ " " ++ toString values)
