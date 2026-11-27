import PairedCycleNormalization
import LongCycleBounds.EulerianSeries
import LongCycleBounds.InsertionBoundary

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open LongCycles LongCycleBounds OpenMathResearch.LongCycleExcedances Real
open scoped PowerSeries

/-- The single admissible cycle contributes its signed Eulerian moment
divided by p!, with the geometric scale R^p. -/
theorem original_paired_single_cycle_coeff {p : ℕ} (hp : 2 ≤ p) (x : ℝ) (hx : 0 ≤ x)
    {R : ℝ} (hR : 0 < R) :
    (R:ℂ)^p*(Band.cycleMoment p x:ℂ)/(p.factorial:ℂ) =
      (∑' q : ℤ, ((pairedPoleDenom (x/R) (π/R) q)⁻¹)^p)/(p:ℂ) := by
  apply paired_single_cycle_normalization x hR (by omega : 0 < p)
  have h := eulerian_eq_oddPoleSum (p-1) (by omega : 1 ≤ p-1) x hx
  simpa only [Band.cycleMoment, Band.moment, sub_neg_eq_add,
    Nat.sub_add_cancel (by omega : 1 ≤ p), oddPoleSum] using h

/-- Coefficientwise convergence of the linear cycle exponent to the actual
signed Eulerian cycle input, including the cutoff and degree-zero cases. -/
theorem original_hasSum_paired_cycle_log_coeff {k : ℕ} (hk : 2 ≤ k) (x : ℝ) (hx : 0 ≤ x)
    {R : ℝ} (hR : 0 < R) (p : ℕ) :
    HasSum (fun q : ℤ => PowerSeries.coeff (R := ℂ) p (pairedCycleLog k (x/R) (π/R) q))
      (if k ≤ p then (R:ℂ)^p*(Band.cycleMoment p x:ℂ)/(p.factorial:ℂ) else 0) := by
  have hS : π/R ≠ 0 := (div_pos pi_pos hR).ne'
  by_cases hp : k ≤ p
  · rw [if_pos hp, original_paired_single_cycle_coeff (hk.trans hp) x hx hR]
    simpa only [if_pos hp] using hasSum_paired_cycle_log_coeff (x/R) hS hk p
  · simpa only [if_neg hp] using hasSum_paired_cycle_log_coeff (x/R) hS hk p

#print axioms original_paired_single_cycle_coeff
#print axioms original_hasSum_paired_cycle_log_coeff
end RepositoryQuotientAudit
