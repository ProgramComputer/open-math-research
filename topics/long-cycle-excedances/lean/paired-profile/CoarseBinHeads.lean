import CoarseBinMoments
import RepositoryRegularCost
import Mathlib.Data.Rat.BigOperators

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset

def regularBinWeightRat (lower b : ℕ) : ℚ :=
  let j := regularBlockIndex lower b
  if 2 ≤ j then 1/(2*(j.factorial:ℚ)) else 1

def valueBinWeightRat (lower b : ℕ) : ℚ :=
  if b+8 ≤ 4*lower then 4/7 else 1

private theorem cast_regularBinWeightRat (lower b : ℕ) :
    (regularBinWeightRat lower b:ℝ) = regularBinWeight lower b := by
  dsimp only [regularBinWeightRat, regularBinWeight]
  split_ifs <;> push_cast <;> norm_num

private theorem cast_valueBinWeightRat (lower b : ℕ) :
    (valueBinWeightRat lower b:ℝ) = valueBinWeight lower b := by
  unfold valueBinWeightRat valueBinWeight
  split_ifs <;> push_cast <;> norm_num

/-- Rational regular cost per bin, with the same cutoff guard and factorial weight. -/
def coarseRegularBinCost (lower upper b : ℕ) (radius : ℚ) : ℚ :=
  if b+5 ≤ 5*upper then
    (regularBinWeightRat lower b/radius)*
      ((coarseZerothTable (coarseShapeIndex (coarseBinY lower upper b)):ℚ)/linearScale)
  else 0

/-- Rational nonprincipal cost per bin, using the signed first-moment units. -/
def coarseNonprincipalBinCost (lower upper b : ℕ) : ℚ :=
  if b+5 ≤ 5*upper then
    valueBinWeightRat lower b*
      ((coarseFirstTable (coarseShapeIndex (coarseBinY lower upper b)):ℚ)/linearScale)
  else 0

theorem regular_bin_cost_le_coarse (lower b : ℕ) {upper : ℕ}
    (hu : 0 < upper) (h48 : upper ≤ 48) {radius : ℚ} (hr : 0 < radius) :
    regularBinCost lower upper b (radius:ℝ) ≤ (coarseRegularBinCost lower upper b radius:ℝ) := by
  by_cases hb : b+5 ≤ 5*upper
  · simp only [regularBinCost,coarseRegularBinCost,if_pos hb]
    push_cast
    rw [cast_regularBinWeightRat]
    exact mul_le_mul_of_nonneg_left (coarse_bin_moments lower upper b hu h48).1
      (div_nonneg (regularBinWeight_nonneg lower b) (by exact_mod_cast hr.le))
  · simp [regularBinCost,coarseRegularBinCost,hb]

theorem nonprincipal_bin_cost_le_coarse (lower b : ℕ) {upper : ℕ}
    (hu : 0 < upper) (h48 : upper ≤ 48) :
    nonprincipalBinCost lower upper b ≤ (coarseNonprincipalBinCost lower upper b:ℝ) := by
  by_cases hb : b+5 ≤ 5*upper
  · simp only [nonprincipalBinCost,coarseNonprincipalBinCost,if_pos hb]
    push_cast
    rw [cast_valueBinWeightRat]
    exact mul_le_mul_of_nonneg_left (coarse_bin_moments lower upper b hu h48).2
      (by unfold valueBinWeight; split <;> norm_num)
  · simp [nonprincipalBinCost,coarseNonprincipalBinCost,hb]

def coarseRegularHead (slab : Fin 9) (lower : ℕ) (q : ℕ→ℕ) : ℚ :=
  ∑ b ∈ range 241,
    coarseRegularBinCost lower (linearSlabX slab) b (linearSlabLower slab)*((q b:ℚ)/linearScale)

def coarseNonprincipalHead (lower upper : ℕ) (q : ℕ→ℕ) : ℚ :=
  ∑ b ∈ range 241, coarseNonprincipalBinCost lower upper b*((q b:ℚ)/linearScale)

theorem regular_head_le_coarse (slab : Fin 9) (lower : ℕ) (q : ℕ→ℕ) :
    regularHeadEstimate slab lower q ≤ (coarseRegularHead slab lower q:ℝ) := by
  have hu : 0 < linearSlabX slab := by fin_cases slab <;> norm_num [linearSlabX]
  have h48 : linearSlabX slab ≤ 48 := by fin_cases slab <;> norm_num [linearSlabX]
  have hr : 0 < linearSlabLower slab := by
    fin_cases slab <;> norm_num [linearSlabLower,linearSlabQuarter]
  unfold regularHeadEstimate coarseRegularHead
  rw [Rat.cast_sum]
  apply sum_le_sum
  intro b _
  push_cast
  exact mul_le_mul_of_nonneg_right (regular_bin_cost_le_coarse lower b hu h48 hr) (by positivity)

theorem nonprincipal_head_le_coarse (lower : ℕ) {upper : ℕ}
    (hu : 0 < upper) (h48 : upper ≤ 48) (q : ℕ→ℕ) :
    nonprincipalHeadEstimate lower upper q ≤ (coarseNonprincipalHead lower upper q:ℝ) := by
  unfold nonprincipalHeadEstimate coarseNonprincipalHead
  rw [Rat.cast_sum]
  apply sum_le_sum
  intro b _
  push_cast
  exact mul_le_mul_of_nonneg_right (nonprincipal_bin_cost_le_coarse lower b hu h48) (by positivity)

#print axioms regular_bin_cost_le_coarse
#print axioms nonprincipal_bin_cost_le_coarse
#print axioms regular_head_le_coarse
#print axioms nonprincipal_head_le_coarse
end OpenMathResearch.LongCycleExcedances
