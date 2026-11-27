import ScaledCycleProfile
import PairedCoefficientLimit
import RepositoryPairedCycleLift
import LongCycleBounds.GeneralCycleSupports

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open Finset Filter LongCycleBounds LongCycleBounds.CycleCount OpenMathResearch.LongCycleExcedances
open scoped PowerSeries Topology

/-- The literal insertion-normalized row is the degree-n coefficient
of the logarithm exponential truncated at the last admissible cycle count. -/
theorem original_scaled_cycle_profile_exp {k : ℕ} (hk : 2 ≤ k)
    (x R : ℝ) (n : ℕ) :
    (∑ h ∈ range (n/k+1), PowerSeries.coeff (R := ℂ) n
      (scaledCycleLog R (fun a => Band.cycleMoment a x) k ^ h) / (h.factorial:ℂ)) =
      (R:ℂ)^n*(Band.normalizedEnumerator n k x:ℂ)/(n.factorial:ℂ) := by
  rw [normalizedEnumerator_ordered_cycle_rows hk]
  exact truncated_exp_eq_scaled_profile_sum R (fun a => Band.cycleMoment a x) k
    (fun n h => orderedMomentRow (fun a => Band.cycleMoment a x) n k h)
    (fun n => orderedMomentRow.eq_1 _ n k) (fun n h => orderedMomentRow.eq_2 _ n k h)
    n (n/k)

/-- The exact normalized original row is the limit of the truncated
exponential coefficients formed from finite subsets of odd poles. -/
theorem tendsto_original_scaled_cycle_profile_exp {k : ℕ} (hk : 2 ≤ k)
    (x : ℝ) (hx : 0 ≤ x) {R : ℝ} (hR : 0 < R) (n : ℕ) :
    Tendsto (fun A : Finset ℤ => ∑ h ∈ range (n/k+1), PowerSeries.coeff (R := ℂ) n
      ((∑ q ∈ A, pairedCycleLog k (x/R) (Real.pi/R) q) ^ h) / (h.factorial:ℂ))
      atTop (𝓝 ((R:ℂ)^n*(Band.normalizedEnumerator n k x:ℂ)/(n.factorial:ℂ))) := by
  rw [←original_scaled_cycle_profile_exp hk x R n]
  apply tendsto_truncated_exp_coeff
  intro p
  simpa only [HasSum, SummationFilter.unconditional, scaledCycleLog, map_sum, PowerSeries.coeff_mk] using
    original_hasSum_paired_cycle_log_coeff hk x hx hR p

#print axioms original_scaled_cycle_profile_exp
#print axioms tendsto_original_scaled_cycle_profile_exp
end RepositoryQuotientAudit
