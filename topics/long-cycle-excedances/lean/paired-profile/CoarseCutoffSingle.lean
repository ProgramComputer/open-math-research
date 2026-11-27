import CutoffSingleSlabs
import CoarseBinMoments
import CoarseStarConstants

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace OpenMathResearch.LongCycleExcedances

/-- The single-primitive entry of the short rational certificate. -/
def coarseCutoffSingle (slab : Fin 9) : ℚ :=
  let index := coarseShapeIndex (1 / (linearSlabX slab : ℚ))
  ((coarseZerothTable index : ℚ) / linearScale) *
    ((coarseStarNumerator slab : ℚ) / 256) /
    (2 * (((cutoffSlabLower slab)-1).factorial : ℚ) * linearSlabLower slab^2)

theorem cutoff_single_le_coarse (slab : Fin 9) :
    cutoffSingleSlabCap slab ≤ coarseCutoffSingle slab := by
  fin_cases slab <;> decide +kernel

#print axioms cutoff_single_le_coarse
end OpenMathResearch.LongCycleExcedances
