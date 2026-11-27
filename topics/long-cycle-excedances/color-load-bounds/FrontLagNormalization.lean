import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false
noncomputable section

namespace OpenMathResearch.LongCycleExcedances
open Real

theorem front_rank_square {n p : ℕ} (hp : p ≤ ⌊sqrt (n:ℝ)/2⌋₊) :
    4*p^2 ≤ n := by
  have h : (p:ℝ) ≤ sqrt (n:ℝ)/2 :=
    (Nat.cast_le.mpr hp).trans (Nat.floor_le (by positivity))
  have h2 : 2*(p:ℝ) ≤ sqrt (n:ℝ) := by linarith
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 2*(p:ℝ)) h2 2
  have hn := Real.sq_sqrt (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  exact_mod_cast (show 4*(p:ℝ)^2 ≤ (n:ℝ) by nlinarith only [hs,hn])

theorem front_sparse_of_large_size {n k : ℕ} (hn : 1 ≤ n) (hk : 0 < k)
    (hsize : 30*log (n:ℝ)+20 < (n:ℝ)/(200*(k:ℝ))) : 4000*k < n := by
  have hlog := Real.log_nonneg (show 1 ≤ (n:ℝ) by exact_mod_cast hn)
  have hk' : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hdiv : (20:ℝ) < (n:ℝ)/(200*(k:ℝ)) := lt_of_le_of_lt (by linarith) hsize
  have hprod := (lt_div_iff₀ (by positivity)).mp hdiv
  exact_mod_cast (show 4000*(k:ℝ) < n by linarith)

theorem front_remove_lag_normalization {L A D : ℝ} (hL : 0 ≤ L) (hA : 0 ≤ A) (hD : 0 < D)
    (h : L/D < (A/D)/8) : |L| ≤ (8/25)*|A| := by
  have h' : L/D < (A/8)/D := by simpa only [div_div, mul_comm D] using h
  have h'' : L < A/8 := (div_lt_div_iff_of_pos_right hD).mp h'
  rw [abs_of_nonneg hL,abs_of_nonneg hA]
  linarith

#print axioms front_rank_square
#print axioms front_sparse_of_large_size
#print axioms front_remove_lag_normalization
end OpenMathResearch.LongCycleExcedances
