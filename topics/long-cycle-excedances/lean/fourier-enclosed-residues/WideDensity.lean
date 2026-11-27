import GammaPeak

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real
open private poisson_peak_succ from GammaPeak in
theorem poisson_peak_le_41m {m : ℕ} (hm : 99 ≤ m) : poissonTerm m m ≤ 41/1000 := by
  induction m,hm using Nat.le_induction with
  | base =>
    have hbase : (2718/1000:ℝ) ≤ exp 1 := by linarith only [exp_one_gt_d9]
    have hp := pow_le_pow_left₀ (by norm_num) hbase 99
    have he : exp (99:ℝ) = (exp 1)^99 := by simpa using exp_nat_mul (1:ℝ) 99
    unfold poissonTerm
    norm_num only [Nat.cast_ofNat]
    rw [exp_neg,he]
    have hl : 0 < (exp 1)^99 := pow_pos (exp_pos _) _
    rw [div_le_iff₀ (by positivity), ←div_eq_inv_mul, div_le_iff₀ hl]
    norm_num [Nat.factorial] at hp ⊢
    linarith only [hp]
  | succ m hm ih => exact (poisson_peak_succ (by omega)).trans ih


theorem wide_vertical_density_budget {k : ℕ} (hk : 100 ≤ k)
    {s : ℝ} (hs : 125/2 ≤ s) :
    π*(31/10)*(∑' i : ℕ, poissonTerm (k-1) (s*(i+1:ℕ))) < 14/25 := by
  have hsum := (gamma_mesh_peak (show 1 ≤ k-1 by omega) (show 0 < s by linarith)).trans
    (add_le_add (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<125/2) hs)
      (poisson_peak_le_41m (show 99 ≤ k-1 by omega)))
  have hPi : π*(31/10) ≤ (3.15:ℝ)*(31/10) :=
    mul_le_mul_of_nonneg_right pi_lt_d2.le (by norm_num)
  exact (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ π*(31/10))).trans_lt
    ((mul_le_mul_of_nonneg_right hPi (by norm_num : (0:ℝ) ≤ 1/(125/2)+41/1000)).trans_lt (by norm_num))

#print axioms poisson_peak_le_41m
#print axioms wide_vertical_density_budget
end OpenMathResearch.LongCycleExcedances
