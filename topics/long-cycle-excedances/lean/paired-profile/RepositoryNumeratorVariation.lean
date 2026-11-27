import CutoffCycleSeriesRecurrence
import RepositoryProbabilityBands

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances.CycleProbability
open Finset
open scoped PowerSeries

/-- The literal numerator coefficients are the cutoff permutation probability
differences. The constant mass of the probability series is removed. -/
def originalNumeratorCoeff (k s : ℕ) : ℝ := numeratorDiff k (originalProbability k) s

theorem coeff_cutoffCycleSeries_eq_originalProbability {k : ℕ} (hk : 2 ≤ k) (s : ℕ) :
    PowerSeries.coeff (R := ℂ) s (cutoffCycleSeries k) = (originalProbability k s:ℂ) :=
  coeff_cutoffCycleSeries_eq_of_spec (originalProbability_spec hk) (by omega) s

theorem coeff_cutoffCycleNumerator_eq_original {k s : ℕ} (hk : 2 ≤ k) :
    PowerSeries.coeff (R := ℂ) s ((cutoffCycleSeries k-1)*(1-PowerSeries.X)) =
      (originalNumeratorCoeff k s:ℂ) :=
  coeff_cutoffCycleNumerator_eq_of_spec (originalProbability_spec hk) (by omega)

theorem originalNumeratorCoeff_below {k s : ℕ} (hs : s < k) :
    originalNumeratorCoeff k s = 0 :=
  numeratorDiff_below _ hs

theorem originalNumeratorCoeff_at_cutoff {k : ℕ} (hk : 2 ≤ k) :
    originalNumeratorCoeff k k = 1/(k:ℝ) :=
  (originalProbability_spec hk).numeratorDiff_at_cutoff (by omega)

theorem originalNumeratorCoeff_between {k s : ℕ} (hk : 2 ≤ k) (hks : k < s)
    (hs : s < 2*k) : originalNumeratorCoeff k s = -1/((s:ℝ)*((s:ℝ)-1)) :=
  (originalProbability_spec hk).numeratorDiff_between hks hs

theorem originalNumeratorCoeff_at_twice {k : ℕ} (hk : 2 ≤ k) :
    originalNumeratorCoeff k (2*k) = (1/(k:ℝ)-1/(2*(k:ℝ)-1))/(2*(k:ℝ)) :=
  (originalProbability_spec hk).numeratorDiff_at_twice (by omega)

theorem originalNumeratorCoeff_at_twice_pos_lt {k : ℕ} (hk : 2 ≤ k) :
    0 < originalNumeratorCoeff k (2*k) ∧ originalNumeratorCoeff k (2*k) < 1/(4*(k:ℝ)^2) :=
  (originalProbability_spec hk).numeratorDiff_at_twice_pos_lt hk

theorem originalNumeratorCoeff_first_block_variation {k : ℕ} (hk : 2 ≤ k) :
    (∑ s ∈ Ico (k+1) (2*k), |originalNumeratorCoeff k s|) = 1/(k:ℝ)-1/(2*(k:ℝ)-1) :=
  (originalProbability_spec hk).first_block_variation (by omega)

theorem originalNumeratorCoeff_factorial_block {k j s : ℕ} (hk : 2 ≤ k)
    (hj : 2 ≤ j) (hlo : j*k < s) (hhi : s ≤ (j+1)*k) :
    |originalNumeratorCoeff k s| ≤ 1/(2*(j.factorial:ℝ)*(k:ℝ)^2) :=
  (originalProbability_spec hk).numeratorDiff_factorial_block (by omega) hj hlo hhi

#print axioms coeff_cutoffCycleSeries_eq_originalProbability
#print axioms coeff_cutoffCycleNumerator_eq_original
#print axioms originalNumeratorCoeff_at_cutoff
#print axioms originalNumeratorCoeff_between
#print axioms originalNumeratorCoeff_at_twice
#print axioms originalNumeratorCoeff_at_twice_pos_lt
#print axioms originalNumeratorCoeff_first_block_variation
#print axioms originalNumeratorCoeff_factorial_block
end OpenMathResearch.LongCycleExcedances.CycleProbability
