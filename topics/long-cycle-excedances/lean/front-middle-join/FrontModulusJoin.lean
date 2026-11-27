import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- A midpoint lower bound for the logarithmic gap of consecutive exterior scales. -/
theorem front_log_midpoint {h : ℝ} (hh : 0 < h) :
    1/(h+1/2) ≤ log (1+1/h) := by
  have hlog := Real.le_log_one_add_of_nonneg (x := 1/h) (by positivity)
  convert hlog using 1
  field_simp
  <;> ring

/-- The last exterior modulus pays for the full factor in the front bound,
with a uniform margin before the first required phase interval. -/
theorem front_separation_log {N h : ℝ} (hh : 0 < h)
    (hbudget : (h+1)^2 ≤ (9/25:ℝ)^2*N) :
    5/2 < N*log (1+1/h) - N/(h+5/6) := by
  have hN : 0 < N := by nlinarith [sq_pos_of_pos (by positivity : 0 < h+1)]
  have hmid := mul_le_mul_of_nonneg_left (front_log_midpoint hh) hN.le
  rw [mul_one_div] at hmid
  have hprod : 0 < (h+1/2)*(h+5/6) := by positivity
  have hgap : N/(h+1/2)-N/(h+5/6) = (N/3)/((h+1/2)*(h+5/6)) := by
    field_simp
    <;> ring
  have hstrict : 5/2 < (N/3)/((h+1/2)*(h+5/6)) := by
    apply (lt_div_iff₀ hprod).2
    nlinarith [sq_nonneg h]
  rw [← hgap] at hstrict
  linarith

private theorem front_log_scale : log (459/40:ℝ) < 5/2 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).2
  have h1 : (8/3:ℝ) < exp 1 := by linarith [Real.exp_one_gt_d9]
  have h5 := pow_lt_pow_left₀ h1 (by norm_num : 0 ≤ (8/3:ℝ)) (by decide : 5 ≠ 0)
  have hs : exp (5/2:ℝ)^2 = exp (1:ℝ)^5 := by
    rw [←Real.exp_nat_mul,←Real.exp_nat_mul]
    congr 1
    norm_num
  nlinarith [Real.exp_pos (5/2:ℝ)]

/-- Separate every exterior radius dominated by the front envelope from the
modulus at the boundary angle. Both moduli refer to the old row. -/
theorem exterior_modulus_lt_phase_boundary {n : ℕ} {h b u : ℝ} (hh : 0 < h)
    (hbudget : (h+1)^2 ≤ (9/25:ℝ)^2*n) (hb : b ≤ (n:ℝ)/(h+5/6))
    (hu : u ≤ (459/40:ℝ)*(h/(h+1))^n) :
    u < exp (-b) := by
  have htlog : log (h/(h+1)) = -log (1+1/h) := by
    rw [← Real.log_inv]
    congr 1
    field_simp
    <;> ring
  have hfront : 0 < (459/40:ℝ)*(h/(h+1))^n := by positivity
  apply hu.trans_lt
  apply (Real.log_lt_iff_lt_exp hfront).1
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow,htlog]
  nlinarith [front_log_scale,front_separation_log hh hbudget]

/-- For the integer number of exterior radii, the squared budget holds
at every old size at least ten thousand. -/
theorem exterior_floor_budget {n : ℕ} (hn : 10000 ≤ n) :
    let h : ℕ := ⌊(7/20:ℝ)*sqrt (n:ℝ)⌋₊
    0 < (h:ℝ) ∧ ((h:ℝ)+1)^2 ≤ (9/25:ℝ)^2*n := by
  dsimp only
  have hn' : (10000:ℝ) ≤ n := by exact_mod_cast hn
  have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  have hsr := Real.sqrt_nonneg (n:ℝ)
  have hs100 : 100 ≤ sqrt (n:ℝ) := by nlinarith
  have hf := Nat.floor_le (show 0 ≤ (7/20:ℝ)*sqrt (n:ℝ) by positivity)
  have hlo := Nat.lt_floor_add_one ((7/20:ℝ)*sqrt (n:ℝ))
  constructor
  · linarith
  · have hb : ((⌊(7/20:ℝ)*sqrt (n:ℝ)⌋₊:ℕ):ℝ)+1 ≤ (9/25:ℝ)*sqrt n := by linarith
    have hsq := pow_le_pow_left₀ (by positivity) hb 2
    nlinarith

#print axioms front_log_midpoint
#print axioms front_separation_log
#print axioms exterior_modulus_lt_phase_boundary
#print axioms exterior_floor_budget
end OpenMathResearch.LongCycleExcedances
