import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- The existing scaled atom implies the rational front bound when
the residual has at least half the trials. -/
theorem modal_bound_two_grids {N d b : ℝ} (hd : 150 ≤ d) (hNd : 2*d ≤ N)
    (hb : 2*√d*√(N-d)*b ≤ √N) : b ≤ 29/500 := by
  have hd0 : 0 < d := by linarith
  have hq : 0 < N-d := by linarith
  have hN : 0 < N := by linarith
  have scale : 0 < 2*√d*√(N-d) := by positivity
  have hs : √N ≤ (2*√d*√(N-d))*(29/500) := by
    apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
    rw [sq_sqrt hN.le, mul_pow, mul_pow, mul_pow, sq_sqrt hd0.le, sq_sqrt hq.le]
    have hp := mul_le_mul_of_nonneg_right hd hq.le
    nlinarith only [hNd,hN,hp]
  by_contra! h
  exact (not_lt_of_ge (hb.trans hs)) (mul_lt_mul_of_pos_left h scale)

/-- The two grids cancel the residual denominator. Using both bounds
preserves the 8/25 target with uniform rational constants. -/
theorem two_grid_relative_lag {a L α : ℝ} (ha : 0 ≤ a)
    (hα : 99/100 ≤ (1+(8/3)*a)*α)
    (hg : L ≤ 1/200 + 29/500)
    (hres : a*L ≤ (151/100)*(1/200 + 29/500)) : L < (8/25)*α := by
  have hsmall : (1+(8/3)*a)*L < (8/25)*(99/100) := by nlinarith only [hg,hres]
  have h := hsmall.trans_le (mul_le_mul_of_nonneg_left hα (by norm_num))
  by_contra! hbad
  have hbad' := mul_le_mul_of_nonneg_left hbad (by positivity : 0 ≤ 1+(8/3:ℝ)*a)
  nlinarith only [h,hbad']

#print axioms modal_bound_two_grids
#print axioms two_grid_relative_lag
end OpenMathResearch.LongCycleExcedances
