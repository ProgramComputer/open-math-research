import GammaPeak

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

private theorem inflation_exp {α : ℝ} (hα : 0 < α) {m k : ℕ}
    (hk : 0 < k) (hm : m ≤ k) : (1+1/(α*(k:ℝ)))^m ≤ exp (1/α) := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have h₀ := add_one_le_exp (1/(α*(k:ℝ)))
  rw [add_comm] at h₀
  have h := pow_le_pow_left₀ (by positivity) h₀ m
  rw [←exp_nat_mul] at h
  apply h.trans (Real.exp_le_exp.mpr _)
  have hcast : (m:ℝ) ≤ k := by exact_mod_cast hm
  rw [mul_one_div,div_le_div_iff₀ (mul_pos hα hk') hα]
  nlinarith [mul_le_mul_of_nonneg_right hcast hα.le]

theorem vertical_radius_power {k : ℕ} (hk : 7 ≤ k) {x r : ℝ} (hr : 0 ≤ r)
    (hx : 10*√(k:ℝ) ≤ x) (hrsq : r^2=x^2+π^2) :
    (r*(1+1/(50*(k:ℝ))))^(k-1) ≤ x^(k-1)*exp (7/100) := by
  have hk' : (0:ℝ) < k := by exact_mod_cast (show 0<k by omega)
  have hxs : 0 ≤ x := (by positivity : 0 ≤ 10*√(k:ℝ)).trans hx
  have hx2 : 100*(k:ℝ) ≤ x^2 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 10*√(k:ℝ)) hx 2
    rw [mul_pow,Real.sq_sqrt hk'.le] at h
    linarith
  let a := 1/(20*(k:ℝ))
  have ha : 0 < a := by dsimp [a]; positivity
  have hpi : π^2 ≤ 10 := (pow_le_pow_left₀ pi_pos.le pi_lt_d2.le 2).trans (by norm_num)
  have hs : π^2 ≤ 2*x^2*a := by
    dsimp [a]
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    nlinarith only [hx2,mul_le_mul_of_nonneg_right hpi (by positivity : 0 ≤ 20*(k:ℝ))]
  have hrad : r ≤ x*(1+a) := by
    apply le_of_sq_le_sq _ (mul_nonneg hxs (by positivity))
    nlinarith only [hrsq,hs,sq_nonneg (x*a)]
  let b := 1/(50*(k:ℝ))
  have hb : 0 ≤ 1+b := by dsimp [b]; positivity
  apply (pow_le_pow_left₀ (mul_nonneg hr hb) (mul_le_mul_of_nonneg_right hrad hb) (k-1)).trans
  rw [mul_pow,mul_pow,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hxs _)
  have ha' : (1+a)^(k-1) ≤ exp (1/20) := inflation_exp (by norm_num) (by omega) (by omega)
  have hb' : (1+b)^(k-1) ≤ exp (1/50) := inflation_exp (by norm_num) (by omega) (by omega)
  have h := mul_le_mul ha' hb' (pow_nonneg hb _) (exp_pos _).le
  rw [←exp_add,show (1/20:ℝ)+1/50=7/100 by norm_num] at h
  exact h

#print axioms vertical_radius_power
end OpenMathResearch.LongCycleExcedances
