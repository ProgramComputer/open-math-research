import ActualOccupiedValue

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Filter Finset
open scoped Topology PowerSeries

/-- The positive coefficient of the finite pole product equals the finite
slice of the marked occupied-configuration sum. -/
theorem finite_actual_occupiedCoeff (A : Finset ℤ) {k N : ℕ} (hN : 0 < N)
    (C : ℝ) {S : ℝ} (hS : S ≠ 0) :
    PowerSeries.coeff (R := ℂ) N (∏ q ∈ A,
      PowerSeries.rescale (pairedPoleDenom C S q)⁻¹ (cutoffCycleSeries k)) =
      ∑ a ∈ A, PowerSeries.coeff (R := ℂ) N (occupiedDistinct k C S a *
        ∏ q ∈ A.erase a, (1+occupiedPrimitive k C S a q)) := by
  simpa only [occupiedDistinct, occupiedPrimitive, pairedPoleDenom_sub] using
    finite_paired_cycle_coeff A C hS (cutoffCycleSeries k) hN

theorem actual_occupiedCoeff_eq_of_product_limit {k N : ℕ} (hk : 3 ≤ k) (hN : 0 < N)
    (C : ℝ) {S : ℝ} (hS : S ≠ 0) {z : ℂ}
    (h : Tendsto (fun A : Finset ℤ => PowerSeries.coeff (R := ℂ) N (∏ q ∈ A,
      PowerSeries.rescale (pairedPoleDenom C S q)⁻¹ (cutoffCycleSeries k))) atTop (𝓝 z)) :
    z = ∑' i, occupiedCoeff (occupiedDistinct k C S) (occupiedPrimitive k C S) N i := by
  have hlim := tendsto_occupiedCoeff_sum (occupiedDistinct k C S) (occupiedPrimitive k C S) N
    (summable_actual_occupiedCoeff hk N C hS)
  simp_rw [finite_actual_occupiedCoeff _ hN C hS] at h
  exact tendsto_nhds_unique h hlim

#print axioms finite_actual_occupiedCoeff
#print axioms actual_occupiedCoeff_eq_of_product_limit
end OpenMathResearch.LongCycleExcedances
