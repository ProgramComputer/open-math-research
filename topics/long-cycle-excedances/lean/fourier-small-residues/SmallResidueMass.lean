import WideOddMass

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

open private odd_le_three_pow from WideOddMass in
theorem small_weighted_mode (j : ℕ) :
    (2*(j:ℝ)+1)*exp (-3*(j:ℝ)) ≤ (1/6:ℝ)^j := by
  have h18 : (18:ℝ) ≤ exp 3 := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 3 by norm_num) 7)
    norm_num [sum_range_succ, Nat.factorial]
  have he : exp (-3:ℝ) ≤ 1/18 := by
    rw [exp_neg,←one_div]
    exact one_div_le_one_div_of_le (by norm_num) h18
  rw [mul_comm (-3:ℝ),exp_nat_mul]
  have h := mul_le_mul (odd_le_three_pow j) (pow_le_pow_left₀ (exp_pos _).le he j)
    (pow_nonneg (exp_pos _).le j) (by positivity : (0:ℝ) ≤ 3^j)
  rw [←mul_pow,show (3:ℝ)*(1/18)=1/6 by norm_num] at h
  exact h

theorem small_weighted_residue_sum (s : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ i ∈ s, f i ≤ exp (-3*((i+1:ℕ):ℝ))) :
    ∑ i ∈ s, (2*((i+1:ℕ):ℝ)+1)*f i ≤ 1/5 := by
  have hs : Summable fun i : ℕ => (1/6:ℝ)^(i+1) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have hgeo : (∑' i : ℕ, (1/6:ℝ)^(i+1)) = 1/5 := by
    simp only [pow_succ,tsum_mul_right,tsum_geometric_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/6) (by norm_num : (1/6:ℝ)<1)]
    norm_num
  refine (sum_le_sum (g := fun i => (1/6:ℝ)^(i+1)) (fun i hi =>
    (mul_le_mul_of_nonneg_left (hf i hi) (by positivity)).trans (small_weighted_mode (i+1)))).trans ?_
  exact (hs.sum_le_tsum s (fun i _ => by positivity)).trans hgeo.le

#print axioms small_weighted_residue_sum
end OpenMathResearch.LongCycleExcedances
