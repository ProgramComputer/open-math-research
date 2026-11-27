import SymmetricPoleComparison
import ProbabilityErrorBands
import RepositoryPairedProductLimit

set_option autoImplicit false
noncomputable section

namespace RepositoryQuotientAudit
open Filter LongCycleBounds OpenMathResearch.LongCycleExcedances
open scoped Topology

/-- The simplified estimate on symmetric finite pole windows passes to the
actual insertion-normalized original permutation rows at both adjacent sizes. -/
theorem original_window_determinant_lower {n k : ℕ} (hk : 2 ≤ k) {u R : ℝ}
    (hu : 0 ≤ u) (hR : 0 < R) (x y δ : ℝ)
    (hwin : ∀ᶠ M in atTop,
      δ ≤ ((x:ℂ)*finiteCoefficient (symmetricPoleWindow M) k (u/R) (Real.pi/R) n -
        (y:ℂ)*finiteCoefficient (symmetricPoleWindow M) k (u/R) (Real.pi/R) (n+1)).re) :
    δ ≤ x*(R^n*Band.normalizedEnumerator n k u/(n.factorial:ℝ)) -
       y*(R^(n+1)*Band.normalizedEnumerator (n+1) k u/((n+1).factorial:ℝ)) := by
  apply determinant_lower_of_symmetric_windows _ _ hwin
  · simpa only [finiteCoefficient,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,
      Complex.ofReal_natCast] using tendsto_original_scaled_finite_paired_products hk u hu hR n
  · simpa only [finiteCoefficient,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,
      Complex.ofReal_natCast] using tendsto_original_scaled_finite_paired_products hk u hu hR (n+1)

#print axioms original_window_determinant_lower
end RepositoryQuotientAudit

namespace OpenMathResearch.LongCycleExcedances.CycleProbability
/-- Centered probability error for the literal minimum-cycle-length permutations.
The degree-zero slot of cutoffWeight is zero, as required in the occupied expansion. -/
theorem original_centered_probability_error {m j N : ℕ} (hk : 100 ≤ m+1)
    (hN : j*(m+1) ≤ N) :
    ((m:ℝ)+1)*|cutoffWeight (m+1) (originalProbability (m+1)) N -
      Real.exp (-cycleHarmonic m)| ≤ centeredErrorBound j :=
  probability_error_bands (originalProbability_spec (by omega)) hk hN

#print axioms original_centered_probability_error
end OpenMathResearch.LongCycleExcedances.CycleProbability
