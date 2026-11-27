import LoadEnvelope
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- x is p/n, M is a binomial grid-atom bound, and L is the normalized
lag coefficient. The two scale assumptions give a uniform relative lag
without ever estimating the residual acceptance probability. -/
theorem sparse_lag_large_budget {n k x M L α : ℝ} (hk : 150 ≤ k) (hsector : 4000*k ≤ n)
    (hx : 0 ≤ x) (hxsmall : x ≤ 1/200) (hgrid : 4*n*x^2 ≤ 1)
    (hatom : (k-1)*M^2 ≤ 1)
    (hlag : L ≤ x+M) (hα : 99/100 ≤ α*(1+(8/3)*k*x)) :
    L < α/8 := by
  have hk0 : 0≤k := by linarith
  have hmesh : k*x^2 ≤ 1/16000 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsector) (sq_nonneg x)]
  have hM12 : M ≤ 1/12 := by
    nlinarith [mul_nonneg (show 0≤k-145 by linarith) (sq_nonneg M), sq_nonneg (M-1/12)]
  have hkM : k*M^2 ≤ 2 := by
    nlinarith [mul_nonneg (show 0≤k-2 by linarith) (sq_nonneg M)]
  have hproduct := mul_le_mul hmesh hkM (by positivity : 0≤k*M^2) (by norm_num)
  have hcross : k*x*M ≤ 1/80 := by
    by_contra! hc
    have hs := mul_self_lt_mul_self (by norm_num : (0:ℝ)≤1/80) hc
    nlinarith only [hproduct,hs]
  have hden : 0 < 1+(8/3)*k*x := by positivity
  have hu : (x+M)*(1+(8/3)*k*x) < (99/100)/8 := by
    nlinarith only [hxsmall,hM12,hmesh,hcross]
  have hp := (mul_le_mul_of_nonneg_right hlag hden.le).trans_lt hu
  by_contra! h
  have hv := mul_le_mul_of_nonneg_right h hden.le
  nlinarith only [hp,hv,hα]

/-- Below the binomial mode, the already checked tail costs at most 1/500. -/
theorem sparse_lag_small_budget {a L α : ℝ} (ha : 0≤a) (hlo : a≤3/4)
    (hlag : L≤1/500) (hα : 99/100 ≤ α*(1+(8/3)*a)) :
    L < α/8 := by
  have hd : 0 < 1+(8/3)*a := by positivity
  have hpos : 0 < α := pos_of_mul_pos_left (lt_of_lt_of_le (by norm_num) hα) hd.le
  have h := mul_le_mul_of_nonneg_left (show 1+(8/3)*a≤3 by linarith) hpos.le
  linarith

#print axioms sparse_lag_large_budget
#print axioms sparse_lag_small_budget
end OpenMathResearch.LongCycleExcedances
