import CoarseFourCost
import CoarseOriginalLedger

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
namespace OpenMathResearch.LongCycleExcedances

/-- Quantitative budget at the least margin surviving all four outward roundings. -/
theorem coarse_nine_margins (s : Fin 9) :
    coarseFourCost s (coarseOriginalLedger s)+93581/10^6 ≤
      (if linearSlabX s ≤ 10 then 54/55 else 6000/12243 : ℚ) := by
  fin_cases s <;> decide +kernel

#print axioms coarse_nine_margins
end OpenMathResearch.LongCycleExcedances
