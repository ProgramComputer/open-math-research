import GammaPeak

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

private theorem poisson_term_frequency {m a : ℕ} (ha : 1 ≤ a) {x : ℝ} (hx : 24 ≤ x)
    (hm : 2*(m:ℝ) ≤ x) : poissonTerm m ((a:ℝ)*x) ≤ (1/10:ℝ)^a := by
  let u : ℝ := (a:ℝ)*x
  have hx' : 0 ≤ x := by linarith
  have ha' : (1:ℝ) ≤ a := by exact_mod_cast ha
  have hu : 0 ≤ u := mul_nonneg (Nat.cast_nonneg a) hx'
  have hmu : 2*(m:ℝ) ≤ u := by
    have := mul_le_mul_of_nonneg_right ha' hx'
    dsimp [u]; linarith
  have htwo : (2:ℝ) ≤ exp (7/10) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (show (0:ℝ)≤7/10 by norm_num) 4)
    norm_num [sum_range_succ,Nat.factorial]
  have hsingle : u^m/(m.factorial:ℝ) ≤ expPrefix m u := by
    exact single_le_sum (f := fun j : ℕ => u^j/(j.factorial:ℝ))
      (fun j _ => by positivity) (self_mem_range_succ m)
  have hpow : (2:ℝ)^m ≤ exp ((m:ℝ)*(7/10)) := by
    rw [exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) htwo m
  have he := (hsingle.trans (expPrefix_half_bound m hu)).trans
    (mul_le_mul_of_nonneg_right hpow (exp_pos _).le)
  rw [←exp_add] at he
  have H := mul_le_mul_of_nonneg_left he (exp_pos (-u)).le
  rw [←exp_add] at H
  have harg : -u+((m:ℝ)*(7/10)+u/2) ≤ (a:ℝ)*(-3) := by
    have hx24 : 24*(a:ℝ) ≤ u := by simpa only [u,mul_comm (a:ℝ)] using mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg a)
    linarith only [hmu,hx24]
  have h3 : (10:ℝ) ≤ exp 3 := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (show (0:ℝ)≤3 by norm_num) 4)
    norm_num [sum_range_succ,Nat.factorial]
  have h3' : exp (-3:ℝ) ≤ 1/10 := by rw [exp_neg,←one_div]; exact one_div_le_one_div_of_le (by norm_num) h3
  have h := (H.trans (exp_le_exp.mpr harg))
  rw [exp_nat_mul] at h
  change exp (-u)*u^m/(m.factorial:ℝ) ≤ _
  rw [mul_div_assoc]
  exact h.trans (pow_le_pow_left₀ (exp_pos _).le h3' a)

theorem all_cutoff_vertical_density_budget {k : ℕ} (hk : 7 ≤ k) {x : ℝ}
    (hx : 10*√(k:ℝ) ≤ x) :
    π*exp (7/100)*(∑' i : ℕ, poissonTerm (k-1) (x*(i+1:ℕ))) < 12/25 := by
  by_cases hlarge : 14 ≤ k
  · exact long_cycle_vertical_density_budget hlarge hx
  have hk' : (7:ℝ) ≤ k := by exact_mod_cast hk
  have hs : 24/10 ≤ √(k:ℝ) := (Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)).mpr (by linarith)
  have hx24 : 24 ≤ x := by linarith
  have hk24 : 2*(k-1:ℕ) ≤ (24:ℕ) := by omega
  have hm : 2*((k-1:ℕ):ℝ) ≤ x := (show 2*((k-1:ℕ):ℝ) ≤ 24 by exact_mod_cast hk24).trans hx24
  let f (i : ℕ) := poissonTerm (k-1) (x*(i+1:ℕ))
  have hf (i : ℕ) : f i ≤ (1/10:ℝ)^(i+1) := by
    simpa only [f,mul_comm x] using poisson_term_frequency (Nat.succ_pos i) hx24 hm
  have hgeo : Summable (fun i : ℕ => (1/10:ℝ)^(i+1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have hsum := (hgeo.of_nonneg_of_le (fun i => show 0 ≤ f i by dsimp [f,poissonTerm]; positivity) hf).tsum_le_tsum hf hgeo
  have hgeom : (∑' i : ℕ, (1/10:ℝ)^(i+1)) = 1/9 := by
    simp only [pow_succ,tsum_mul_right,tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/10) (by norm_num : (1/10:ℝ)<1)]
    norm_num
  rw [hgeom] at hsum
  have he : exp (7/100:ℝ) ≤ 100/93 := by
    have h := mul_le_mul_of_nonneg_right (add_one_le_exp (-(7/100:ℝ))) (exp_pos (7/100:ℝ)).le
    rw [←exp_add,neg_add_cancel,exp_zero] at h
    linarith
  have hC := mul_le_mul pi_lt_d2.le he (exp_pos _).le (by norm_num : (0:ℝ) ≤ 3.15)
  exact (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ π*exp (7/100))).trans_lt
    ((mul_le_mul_of_nonneg_right hC (by norm_num : (0:ℝ) ≤ 1/9)).trans_lt (by norm_num))

#print axioms all_cutoff_vertical_density_budget
end OpenMathResearch.LongCycleExcedances
