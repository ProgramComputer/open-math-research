import CoarseAtomSubtraction
import CoarseBinHeads
import CoarseCutoffSingle
import PrincipalCostBridge
import FourWindowErrors

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances
open Finset

def coarsePrincipalCost (lower : ℕ) (q : ℕ→ℕ) : ℚ :=
  2*(∑ b ∈ range 241, rationalCenteredError (centeredBinIndex lower b)*((q b:ℚ)/linearScale))+1/10000

theorem coarse_principal_cost_cast (lower : ℕ) (q : ℕ→ℕ) :
    (coarsePrincipalCost lower q:ℝ) = principalHeadEstimate lower q := by
  unfold coarsePrincipalCost principalHeadEstimate
  push_cast
  simp only [rationalCenteredError_cast]

def coarseFourCost (slab : Fin 9) (q : ℕ→ℕ) : ℚ :=
  let lower := cutoffSlabLower slab
  coarsePrincipalCost lower q + coarseNonprincipalHead lower (linearSlabX slab) q +
    coarseRegularHead slab lower q + (coarseCutoffSingle slab + coarseMultipleCost slab lower q)

theorem four_cost_le_coarse (slab : Fin 9) (q : ℕ→ℕ) (hq : q 0=linearScale)
    (hrec : ∀ m < 240, ∑ ij ∈ antidiagonal m,
      (ij.1+1)*linearSlabTable slab (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*linearScale) :
    fourErrorHead slab q ≤ (coarseFourCost slab q:ℝ) := by
  let lower := cutoffSlabLower slab
  have hx : linearSlabX slab ≤ 48 := by fin_cases slab <;> norm_num [linearSlabX]
  have hu : 0 < linearSlabX slab := by fin_cases slab <;> norm_num [linearSlabX]
  have hn := nonprincipal_head_le_coarse lower hu hx q
  have hr := regular_head_le_coarse slab lower q
  have ha := coarse_multiple_cost_upper slab lower q hq hrec
  have hs := Rat.cast_le (K:=ℝ) |>.mpr (cutoff_single_le_coarse slab)
  unfold fourErrorHead coarseFourCost
  push_cast
  rw [coarse_principal_cost_cast]
  exact add_le_add (add_le_add (add_le_add le_rfl hn) hr) (add_le_add hs ha)

#print axioms coarse_principal_cost_cast
#print axioms four_cost_le_coarse
end OpenMathResearch.LongCycleExcedances
