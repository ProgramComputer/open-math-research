import LiteralLinearTable

open OpenMathResearch.LongCycleExcedances

-- Executable comparison only. The inequality proof does not depend on evaluation.
#eval do
  for (x, quarter) in ([(6,73),(10,43),(16,27),(22,19),(28,15),
      (34,12),(40,10),(44,9),(48,9)] : List (ℕ × ℕ)) do
    let values := (List.range 241).map (literalLinearTable (10000/x) x ((quarter:ℚ)/4))
    IO.println (toString x ++ " " ++ toString values)
