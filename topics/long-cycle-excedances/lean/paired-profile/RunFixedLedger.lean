import FixedPrincipalCaps
open OpenMathResearch.LongCycleExcedances
#eval (List.finRange 9).forM fun slab => do
  IO.println s!"{linearSlabX slab} {(principalQLedger slab).toList}"
