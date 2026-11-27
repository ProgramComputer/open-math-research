import TwoGridLag
import ZeroResidualLag
import OriginalResidualLag
import RepositoryBinomialGrid

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open Finset LongCycles PowerSeries OpenMathResearch.LongCycleExcedances

theorem original_front_lag_zero_at_high_cutoff {n k p : ℕ} (hk : 2 ≤ k)
    (hkn : k ≤ n) (hcut : n+1 < 2*k) :
    (originalFrontLag n k).coeff p = 0 := by
  have hm : 0 < n+1-k := by omega
  have h := original_color_successor_lag (n:=n) hk p
  have hu := h.2
  rw [original_color_successor_exact hk (by omega : k ≤ n+1) p] at hu
  apply front_lag_zero_of_residual_count hk hkn hcut h.1
  have hterm (j : ℕ) : coeff (R := ℝ) (p-j)
      (colorTransform (n+1-k) (enumerator (n+1-k) k)) =
      ColorAnchor.realCount (n+1-k) (p-j) k :=
    (original_color_count_eq_transform hm hk).symm
  simpa only [hterm] using hu

theorem original_front_lag_relative_of_alpha {n k p : ℕ} (hn : 10000 ≤ n)
    (hk : 2 ≤ k) (hkn : k ≤ n) (hp : 0 < p) (hrank : 4*p^2 ≤ n)
    (hα : (99:ℝ)/(100*(1+(8/3)*((k:ℝ)*p/n))) ≤
      (enumerator n k).coeff p/(p:ℝ)^n) :
    (originalFrontLag n k).coeff p < (8/25)*(enumerator n k).coeff p := by
  have hpow : 0 < (p:ℝ)^n := pow_pos (Nat.cast_pos.mpr hp) _
  have hnrm : (originalFrontLag n k).coeff p/(p:ℝ)^n <
      (8/25)*((enumerator n k).coeff p/(p:ℝ)^n) := by
    by_cases hhalf : 2*k ≤ n+1
    · let atom := frozen_band_binomial_atom
      exact sharp_front_lag_of_two_color_grids (fun {A B N} hA hB hN {u v} hu hv => @atom A B N hA hB hN u v hu hv) hn hk hkn hp hrank
        (by omega) (original_lag_le_color_grid hp hk hkn)
        (original_lag_residual_grid hk hp hhalf (front_grid_scale hn hrank)) hα
    · rw [original_front_lag_zero_at_high_cutoff hk hkn (by omega), zero_div]
      exact mul_pos (by norm_num) (lt_of_lt_of_le (by positivity) hα)
  rw [←mul_div_assoc] at hnrm
  exact (div_lt_div_iff_of_pos_right hpow).mp hnrm

#print axioms original_front_lag_zero_at_high_cutoff
#print axioms original_front_lag_relative_of_alpha
end RepositoryQuotientAudit
