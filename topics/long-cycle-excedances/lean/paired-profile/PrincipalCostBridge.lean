import PrincipalCostTable
import RepositoryPrincipalSlab

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances
open Finset CycleProbability

theorem rationalCenteredError_cast (j : ℕ) :
    (rationalCenteredError j : ℝ) = centeredErrorBound j := by
  unfold rationalCenteredError centeredErrorBound
  split
  · norm_num
  split
  · norm_num
  rw [Rat.cast_min]
  push_cast
  split <;> push_cast <;> rfl

theorem roundedSlabQ_recurrence (slab : Fin 9) :
    ∀ m < 240,
      ∑ ij ∈ antidiagonal m,
        (ij.1+1)*linearSlabTable slab (ij.1+1)*roundedQ linearScale (linearSlabTable slab) ij.2 ≤
        (m+1)*roundedQ linearScale (linearSlabTable slab) (m+1)*linearScale := by
  apply bin_ceiling_recurrence (by decide : 0 < linearScale)
  intro m _
  exact roundedQ_step _ _ m

theorem principalHeadEstimate_le_computed_cap (slab : Fin 9) :
    principalHeadEstimate (principalLower slab) (roundedQ linearScale (linearSlabTable slab)) ≤
      (principalMillionths slab : ℝ) / 1000000 := by
  have hc : (rationalPrincipalCost slab : ℝ) ≤ (principalMillionths slab : ℝ) / 1000000 := by
    have h : (rationalPrincipalCost slab : ℝ) ≤
        (((principalMillionths slab : ℚ) / 1000000 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (rationalPrincipalCost_le_millionths slab)
    simpa using h
  convert hc using 1
  unfold principalHeadEstimate rationalPrincipalCost
  push_cast
  rw [add_comm]
  congr 1
  congr 1
  apply sum_congr rfl
  intro b hb
  have hbl : b ≤ 240 := by simp only [mem_range] at hb; omega
  rw [qSlabPrefix_get slab hbl, rationalCenteredError_cast, centeredBinIndex]

/-- The original principal cost uses the certified recurrence and exact computed ceiling. -/
theorem original_slab_principal_le_computed_cap (slab : Fin 9) {j n : ℕ}
    (hn : 10000 ≤ n) (hnX : n ≤ linearSlabX slab * (j+2))
    (hlo : principalLower slab * (j+2) ≤ n) {θ : ℝ}
    (hS : 0 < Real.sin θ) (hU : 6/5 ≤ (n:ℝ)*Real.sin θ^2) (A : Finset ℤ) :
    doubledPrincipalError j n (originalProbability (j+2)) A θ <
      (principalMillionths slab : ℝ) / 1000000 :=
  (original_slab_principal_head_tail slab hn hnX hlo hS hU A
    (roundedQ linearScale (linearSlabTable slab)) (roundedQ_zero _ _)
    (roundedSlabQ_recurrence slab)).trans_le (principalHeadEstimate_le_computed_cap slab)

#print axioms original_slab_principal_le_computed_cap
#print axioms rationalCenteredError_cast
#print axioms roundedSlabQ_recurrence
#print axioms principalHeadEstimate_le_computed_cap
end OpenMathResearch.LongCycleExcedances
