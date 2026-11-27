import RadiusGeometry
import UniformDiscreteTilt

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

theorem actual_linear_absolute {x R : ℝ} (hR : 0 ≤ R) :
    |(-(-exp (-x))/(1-(-exp (-x))))*R| = exp (-x)*R/(1+exp (-x)) := by
  rw [neg_neg,sub_neg_eq_add,abs_of_nonneg (by positivity)]
  ring

theorem small_linear_cost {x r : ℝ} {k : ℕ} (hx : 0 ≤ x) (hx' : x ≤ 10) (hr : 0 ≤ r)
    (hgeom : r^2=x^2+π^2) (hk : 7 ≤ k) :
    let R := r*(1+1/(50*(k:ℝ)))
    |(-(-exp (-x))/(1-(-exp (-x))))*R| ≤ 6 := by
  have hks : (7:ℝ) ≤ k := by exact_mod_cast hk
  have hfactor : 1/(50*(k:ℝ)) ≤ 1/350 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hh : r ≤ 11 := by
    have h1 := pow_le_pow_left₀ hx hx' 2
    have h2 := pow_le_pow_left₀ pi_pos.le pi_lt_d2.le 2
    nlinarith only [hgeom,h1,h2,sq_nonneg (r-11)]
  have hrad : r*(1+1/(50*(k:ℝ))) ≤ 12 := by
    have H := mul_le_mul hh (add_le_add_left hfactor 1) (by positivity) (by norm_num : (0:ℝ)≤11)
    linarith
  have hq := exp_le_one_iff.mpr (neg_nonpos.mpr hx)
  dsimp only
  rw [actual_linear_absolute (by positivity),div_le_iff₀ (by positivity)]
  nlinarith only [mul_le_mul_of_nonneg_left hrad (exp_pos (-x)).le,hq]

theorem large_linear_cost {x R : ℝ} (hx : 10 ≤ x) (hR : 0 ≤ R) (h : R ≤ (53/50)*x) :
    |(-(-exp (-x))/(1-(-exp (-x))))*R| ≤ 1 := by
  have hx' : 0 ≤ x := by linarith
  have hz := Real.sum_le_exp_of_nonneg hx' 3
  norm_num [Finset.sum_range_succ,Nat.factorial] at hz
  have hr : R ≤ exp x := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) hx']
  rw [actual_linear_absolute hR,div_le_iff₀ (by positivity)]
  have he := mul_le_mul_of_nonneg_left hr (exp_pos (-x)).le
  rw [←exp_add,neg_add_cancel,exp_zero] at he
  linarith [exp_pos (-x)]

#print axioms small_linear_cost
#print axioms large_linear_cost
end OpenMathResearch.LongCycleExcedances
