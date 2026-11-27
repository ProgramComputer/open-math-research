import CoarseStarConstants

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 5000000
namespace OpenMathResearch.LongCycleExcedances

theorem coarseStar_bound (slab : Fin 9) :
    linearHead (coarseStarShape slab) + linearHalfTail (coarseStarShape slab) ≤
      coarseStarNumerator slab * (linearScale / 256) := by
  fin_cases slab <;> decide +kernel

#print axioms coarseStar_bound
end OpenMathResearch.LongCycleExcedances
