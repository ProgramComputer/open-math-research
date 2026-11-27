import RepositoryUniformLag
import FrontLagNormalization

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open LongCycles PowerSeries OpenMathResearch.LongCycleExcedances

/-- The next transformed row has at most p^(n+1) color words after division
by the number of color orders. This bounds every original lag coefficient. -/
theorem original_global_lag_bound {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k) (p : ℕ) :
    0 ≤ (originalFrontLag n k).coeff p ∧ (originalFrontLag n k).coeff p ≤ (p:ℝ)^(n+1) := by
  have h := original_color_successor_lag (n:=n) hk p
  change 0 ≤ (originalFrontLag n k).coeff p ∧ (originalFrontLag n k).coeff p ≤
    coeff (R := ℝ) p (colorTransform (n+1) (enumerator (n+1) k)) -
      (p:ℝ)*coeff (R := ℝ) p (colorTransform n (enumerator n k)) at h
  rw [←original_color_count_eq_transform (n:=n+1) (by omega) hk,
      ←original_color_count_eq_transform hn hk] at h
  have hprod := mul_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) (ColorAnchor.realCount_bounds n p k).1
  exact ⟨h.1,(h.2.trans (sub_le_self _ hprod)).trans (ColorAnchor.realCount_bounds (n+1) p k).2⟩

/-- The near-lag hypothesis of the exterior reduction, including rank zero. -/
theorem original_exterior_near_lag {n k : ℕ} (hn : 10000 ≤ n) (hk : 8 ≤ k)
    (hsize : 30*Real.log (n:ℝ)+20 < (n:ℝ)/(200*(k:ℝ)))
    (p : ℕ) (hp : p ≤ ⌊Real.sqrt (n:ℝ)/2⌋₊) :
    |(originalFrontLag n k).coeff p| ≤ (8/25)*|(enumerator n k).coeff p| := by
  have lag := original_global_lag_bound (by omega : 0 < n) (by omega : 2 ≤ k) p
  have hA : 0 ≤ (enumerator n k).coeff p := (RunColors.original_coeff_envelope n k p (by omega)).1
  rcases Nat.eq_zero_or_pos p with rfl|hp0
  · have hz : (originalFrontLag n k).coeff 0 ≤ 0 := by simpa using lag.2
    rw [abs_of_nonneg lag.1,abs_of_nonneg hA]
    linarith
  · have hs := front_sparse_of_large_size (by omega : 1 ≤ n) (by omega : 0 < k) hsize
    exact front_remove_lag_normalization lag.1 hA (pow_pos (Nat.cast_pos.mpr hp0) n)
      (original_uniform_front_lag hn hk hs hp0 (front_rank_square hp))

#print axioms original_global_lag_bound
#print axioms original_exterior_near_lag
end RepositoryQuotientAudit
