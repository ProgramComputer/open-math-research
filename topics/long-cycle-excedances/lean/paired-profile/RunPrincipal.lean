import PrincipalCostTable
open OpenMathResearch.LongCycleExcedances
set_option maxRecDepth 10000
#eval (List.finRange 9).forM fun slab => do
  let Q := qSlabPrefix slab 240
  IO.println s!"{linearSlabX slab} {Q.toList}"
