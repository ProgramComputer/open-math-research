import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

private theorem exp_ten_and_thirteen : (10000:ℝ)<exp 10 ∧ (130000:ℝ)<exp 13 := by
  have h : (27/10:ℝ)<exp 1 := by linarith only [Real.exp_one_gt_d9]
  have he (j : ℕ) : exp (j:ℝ)=(exp 1)^j := by simpa using Real.exp_nat_mul 1 j
  constructor
  · rw [show (10:ℝ)=((10:ℕ):ℝ) by norm_num,he]
    exact (by norm_num : (10000:ℝ)<(27/10:ℝ)^10).trans_le (pow_le_pow_left₀ (by norm_num) h.le 10)
  · rw [show (13:ℝ)=((13:ℕ):ℝ) by norm_num,he]
    exact (by norm_num : (130000:ℝ)<(27/10:ℝ)^13).trans_le (pow_le_pow_left₀ (by norm_num) h.le 13)

/-- A direct Cauchy envelope for small cutoffs gains a full factor of n.
All three numerator budgets work with the same
radial decay rate 4/5. -/
theorem small_cutoff_cauchy_decay {n k M : ℝ} (hn : 10000≤n) (hk : 0<k)
    (hcases : (k≤100 ∧ M≤32) ∨ (k≤50 ∧ M≤60) ∨ (k≤10 ∧ M≤100)) :
    1300*n^2*exp (M-(4/5)*(n/k)) < 1/(100*n) := by
  have hn' : 0<n := by linarith
  have hl := log_le_sub_one_of_pos (show 0<n/10000 by positivity)
  rw [log_div hn'.ne' (by norm_num)] at hl
  have hten := (log_lt_iff_lt_exp (by norm_num : (0:ℝ)<10000)).mpr exp_ten_and_thirteen.1
  have hmargin : M+13+3*log n < (4/5)*(n/k) := by
    rcases hcases with h | h | h
    · have hdiv : n/100 ≤ n/k := div_le_div_of_nonneg_left hn'.le hk h.1
      linarith only [hl,hten,h.2,hn,hdiv]
    · have hdiv : n/50 ≤ n/k := div_le_div_of_nonneg_left hn'.le hk h.1
      linarith only [hl,hten,h.2,hn,hdiv]
    · have hdiv : n/10 ≤ n/k := div_le_div_of_nonneg_left hn'.le hk h.1
      linarith only [hl,hten,h.2,hn,hdiv]
  have hcost : exp (M-(4/5)*(n/k))*exp 13*n^3<1 := by
    have he : exp (M-(4/5)*(n/k))*exp 13*n^3 = exp (M-(4/5)*(n/k)+13+3*log n) := by
      rw [exp_add,exp_add,show (3:ℝ)=((3:ℕ):ℝ) by norm_num,exp_nat_mul,exp_log hn']
    rw [he,←exp_zero]
    exact exp_lt_exp.mpr (by linarith only [hmargin])
  have hcomp := mul_le_mul_of_nonneg_right exp_ten_and_thirteen.2.le
    (mul_nonneg (exp_pos (M-(4/5)*(n/k))).le (pow_nonneg hn'.le 3))
  apply (lt_div_iff₀ (by positivity : 0<100*n)).mpr
  nlinarith only [hcomp,hcost]

/-- In the angular region the direct Cauchy error is also bounded at the
sine scale, including the smallest permitted sine. -/
theorem small_cutoff_cauchy_sine_error {n k M S : ℝ} (hn : 10000≤n) (hk : 0<k)
    (hcases : (k≤100 ∧ M≤32) ∨ (k≤50 ∧ M≤60) ∨ (k≤10 ∧ M≤100)) (hS : 0≤S) (hmid : 1≤n*S^2) :
    1300*n^2*exp (M-(4/5)*(n/k)) < S/100 := by
  have hn0 : 0<n := by linarith
  have hscale : 1≤n*S := by
    rcases le_or_gt S 1 with hs | hs
    · have hsq : S^2 ≤ S := by nlinarith only [mul_nonneg hS (sub_nonneg.mpr hs)]
      exact hmid.trans (mul_le_mul_of_nonneg_left hsq hn0.le)
    · exact (by linarith : (1:ℝ)≤n).trans (le_mul_of_one_le_right hn0.le hs.le)
  apply (small_cutoff_cauchy_decay hn hk hcases).trans_le
  apply (div_le_div_iff₀ (by positivity : 0<100*n) (by norm_num : (0:ℝ)<100)).mpr
  nlinarith only [hscale]

#print axioms small_cutoff_cauchy_sine_error
#print axioms small_cutoff_cauchy_decay
end OpenMathResearch.LongCycleExcedances
