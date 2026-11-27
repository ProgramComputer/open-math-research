import CoarseNineMargins
import CoarseOriginalLedger

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances

theorem coarse_four_budget (slab : Fin 9) :
    fourErrorHead slab (coarseOriginalLedger slab) + 93581/10^6 ≤
      (if linearSlabX slab ≤ 10 then 54/55 else 6000/12243 : ℝ) := by
  have hq := coarseOriginalLedger_zero slab
  have hr := coarseOriginalLedger_recurrence slab
  have h := four_cost_le_coarse slab (coarseOriginalLedger slab) hq hr
  have hu : coarseFourCost slab (coarseOriginalLedger slab)+93581/10^6 ≤
      (if linearSlabX slab ≤ 10 then 54/55 else 6000/12243 : ℚ) := coarse_nine_margins slab
  have hu' := (Rat.cast_le (K:=ℝ)).mpr hu
  push_cast at hu'
  apply (add_le_add h (le_rfl (a:=93581/10^6))).trans
  split_ifs at hu' ⊢ <;> simpa using hu'

#print axioms coarse_four_budget
end OpenMathResearch.LongCycleExcedances
