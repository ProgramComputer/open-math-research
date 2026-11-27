import GammaDensity
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Complex.ExponentialBounds

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

private theorem poisson_peak_succ {m : ℕ} (hm : 0 < m) :
    poissonTerm (m+1) (m+1:ℕ) ≤ poissonTerm m m := by
  have hv : (0:ℝ) < m := by exact_mod_cast hm
  have hinc : 1+1/(m:ℝ) ≤ exp (1/(m:ℝ)) := by linarith [add_one_le_exp (1/(m:ℝ))]
  have hp : (1+1/(m:ℝ))^m ≤ exp 1 := by
    have h := pow_le_pow_left₀ (by positivity) hinc m
    rw [← exp_nat_mul, mul_one_div,div_self hv.ne'] at h
    exact h
  have hs : ((m:ℝ)+1)^m ≤ (m:ℝ)^m*exp 1 := by
    have H := mul_le_mul_of_nonneg_left hp (pow_nonneg hv.le m)
    rw [←mul_pow, mul_add, mul_one, mul_one_div, div_self hv.ne'] at H
    exact H
  have hd : exp (-((m:ℝ)+1))*exp 1 = exp (-(m:ℝ)) := by rw [←exp_add]; congr 1; ring
  unfold poissonTerm
  push_cast
  rw [pow_succ,Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ]
  calc
    _ = exp (-((m:ℝ)+1))*((m:ℝ)+1)^m/m.factorial := by field_simp <;> ring
    _ ≤ exp (-((m:ℝ)+1))*((m:ℝ)^m*exp 1)/m.factorial :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (exp_pos _).le) (by positivity)
    _ = _ := by rw [←hd]; ring

theorem poisson_peak_le_ninth {m : ℕ} (hm : 13 ≤ m) : poissonTerm m m ≤ 1/9 := by
  induction m,hm using Nat.le_induction with
  | base =>
    have hbase : (2718/1000:ℝ) ≤ exp 1 := by linarith only [exp_one_gt_d9]
    have hp := pow_le_pow_left₀ (by norm_num) hbase 13
    have he : exp (13:ℝ) = (exp 1)^13 := by simpa using exp_nat_mul (1:ℝ) 13
    unfold poissonTerm
    norm_num only [Nat.cast_ofNat]
    rw [exp_neg,he]
    have hl : 0 < (exp 1)^13 := pow_pos (exp_pos _) _
    rw [div_le_iff₀ (by positivity), ←div_eq_inv_mul, div_le_iff₀ hl]
    norm_num [Nat.factorial] at hp ⊢
    linarith only [hp]
  | succ m hm ih => exact (poisson_peak_succ (by omega)).trans ih

theorem long_cycle_vertical_density_budget {k : ℕ} (hk : 14 ≤ k)
    {x : ℝ} (hx : 10*√(k:ℝ) ≤ x) :
    π*exp (7/100)*(∑' i : ℕ, poissonTerm (k-1) (x*(i+1:ℕ))) < 12/25 := by
  have hk' : (14:ℝ) ≤ k := by exact_mod_cast hk
  have hs : 37/10 ≤ √(k:ℝ) := (Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)).mpr (by linarith)
  have hx' : 37 ≤ x := by linarith
  have hsum := (gamma_mesh_peak (show 1 ≤ k-1 by omega) (show 0 < x by linarith)).trans
    (add_le_add (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<37) hx')
      (poisson_peak_le_ninth (show 13 ≤ k-1 by omega)))
  have hE : exp (7/100:ℝ) ≤ 100/93 := by
    have h := mul_le_mul_of_nonneg_right (add_one_le_exp (-(7/100:ℝ))) (exp_pos (7/100:ℝ)).le
    rw [←exp_add,neg_add_cancel,exp_zero] at h
    linarith
  have hC := mul_le_mul pi_lt_d2.le hE (exp_pos _).le (by norm_num : (0:ℝ) ≤ 3.15)
  exact (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ π*exp (7/100))).trans_lt
    ((mul_le_mul_of_nonneg_right hC (by norm_num : (0:ℝ) ≤ 1/37+1/9)).trans_lt (by norm_num))

#print axioms poisson_peak_le_ninth
#print axioms long_cycle_vertical_density_budget
end OpenMathResearch.LongCycleExcedances
