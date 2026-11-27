import PairedExpProduct
import RepositoryScaledCycleProfile

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open Finset Filter LongCycleBounds OpenMathResearch.LongCycleExcedances
open scoped PowerSeries Topology

/-- The actual finite products tend coefficientwise to the original
insertion-normalized row, including degree zero and degrees below k. -/
theorem tendsto_original_scaled_finite_paired_products {k : ℕ} (hk : 2 ≤ k)
    (x : ℝ) (hx : 0 ≤ x) {R : ℝ} (hR : 0 < R) (n : ℕ) :
    Tendsto (fun A : Finset ℤ => PowerSeries.coeff (R := ℂ) n (∏ q ∈ A,
      PowerSeries.rescale (pairedPoleDenom (x/R) (Real.pi/R) q)⁻¹ (cutoffCycleSeries k)))
      atTop (𝓝 ((R:ℂ)^n*(Band.normalizedEnumerator n k x:ℂ)/(n.factorial:ℂ))) := by
  simpa only [finite_paired_product_eq_truncated_exp (by omega : 0 < k)] using
    tendsto_original_scaled_cycle_profile_exp hk x hx hR n

#print axioms tendsto_original_scaled_finite_paired_products
end RepositoryQuotientAudit
