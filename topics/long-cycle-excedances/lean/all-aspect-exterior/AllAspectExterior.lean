import RepositorySharpNearLag
import RepositoryAllAspectExterior

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open LongCycles Real OpenMathResearch.LongCycleExcedances

/-- The original exterior near-lag hypothesis for every admissible
cutoff at these sizes, including rank zero. -/
theorem original_near_lag_all_aspects {n k : ℕ} (hn : 10000 ≤ n) (hk : 2 ≤ k)
    (hkn : k ≤ n) (p : ℕ) (hp : p ≤ ⌊sqrt (n:ℝ)/2⌋₊) :
    |(originalFrontLag n k).coeff p| ≤ (8/25)*|(enumerator n k).coeff p| := by
  have lag := original_global_lag_bound (by omega : 0 < n) hk p
  have hA : 0 ≤ (enumerator n k).coeff p := (RunColors.original_coeff_envelope n k p hk).1
  rw [abs_of_nonneg lag.1, abs_of_nonneg hA]
  rcases Nat.eq_zero_or_pos p with rfl|hp0
  · have hz : (originalFrontLag n k).coeff 0 ≤ 0 := by simpa using lag.2
    linarith
  · have hrank := front_rank_square hp
    exact (original_front_lag_relative_of_alpha hn hk hkn hp0 hrank
      (original_front_alpha_lower_all hn hk hkn hp0 hrank)).le

/-- Existence and strict ordering of H old roots, with prescribed signs
in the actual successor, before the first integer phase level. -/
theorem original_all_aspect_exterior {n k : ℕ} (hn : 10000 ≤ n)
    (hk : 2 ≤ k) (hkn : k ≤ n) :
    ∃ f : Fin (uniformJoinRank n) → ℝ, StrictMono f ∧ ∀ i,
      0 < f i ∧ f i < exp (-exteriorIntegerSeamLog n) ∧
      (enumerator n k).eval (-f i) = 0 ∧
      0 < (-1:ℝ)^(i.val+2)*(enumerator (n+1) k).eval (-f i) :=
  original_exterior_roots_before_integer_seam hn hk hkn (original_near_lag_all_aspects hn hk hkn)

#print axioms original_near_lag_all_aspects
#print axioms original_all_aspect_exterior
end RepositoryQuotientAudit
