import GammaPeak

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real
open private poisson_peak_succ from GammaPeak in
theorem poisson_peak_le_four_25 {m : ℕ} (hm : 7 ≤ m) : poissonTerm m m ≤ 4/25 := by
  induction m,hm using Nat.le_induction with
  | base =>
    have hbase : (2718/1000:ℝ) ≤ exp 1 := by linarith only [exp_one_gt_d9]
    have hp := pow_le_pow_left₀ (by norm_num) hbase 7
    have he : exp (7:ℝ) = (exp 1)^7 := by simpa using exp_nat_mul (1:ℝ) 7
    unfold poissonTerm
    norm_num only [Nat.cast_ofNat]
    rw [exp_neg,he]
    have hl : 0 < (exp 1)^7 := pow_pos (exp_pos _) _
    rw [div_le_iff₀ (by positivity), ←div_eq_inv_mul, div_le_iff₀ hl]
    norm_num [Nat.factorial] at hp ⊢
    linarith only [hp]
  | succ m hm ih => exact (poisson_peak_succ (by omega)).trans ih


theorem small_mid_vertical_budget {k : ℕ} (hk : 8 ≤ k)
    {s : ℝ} (hs : 17 ≤ s) :
    π*(31/10)*(∑' i : ℕ, poissonTerm (k-1) (s*(i+1:ℕ))) < 9/4 := by
  have hsum := (gamma_mesh_peak (show 1 ≤ k-1 by omega) (show 0 < s by linarith)).trans
    (add_le_add (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<17) hs)
      (poisson_peak_le_four_25 (show 7 ≤ k-1 by omega)))
  have hPi : π*(31/10) ≤ (3.15:ℝ)*(31/10) :=
    mul_le_mul_of_nonneg_right pi_lt_d2.le (by norm_num)
  exact (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ π*(31/10))).trans_lt
    ((mul_le_mul_of_nonneg_right hPi (by norm_num : (0:ℝ) ≤ 1/(17)+4/25)).trans_lt (by norm_num))


private theorem far_poisson_term_frequency {m a : ℕ} (ha : 1 ≤ a) {x : ℝ} (hx : 200 ≤ x)
    (hm : 2*(m:ℝ) ≤ x) : poissonTerm m ((a:ℝ)*x) ≤ (1/101:ℝ)^a := by
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
  have harg : -u+((m:ℝ)*(7/10)+u/2) ≤ (a:ℝ)*(-6) := by
    have hx200 : 200*(a:ℝ) ≤ u := by simpa only [u,mul_comm (a:ℝ)] using mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg a)
    linarith only [hmu,hx200]
  have h3 : (101:ℝ) ≤ exp 6 := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (show (0:ℝ)≤6 by norm_num) 6)
    norm_num [sum_range_succ,Nat.factorial]
  have h3' : exp (-6:ℝ) ≤ 1/101 := by rw [exp_neg,←one_div]; exact one_div_le_one_div_of_le (by norm_num) h3
  have h := (H.trans (exp_le_exp.mpr harg))
  rw [exp_nat_mul] at h
  change exp (-u)*u^m/(m.factorial:ℝ) ≤ _
  rw [mul_div_assoc]
  exact h.trans (pow_le_pow_left₀ (exp_pos _).le h3' a)

theorem small_far_vertical_budget {k : ℕ} (hk : k ≤ 99) {x : ℝ} (hx : 200 ≤ x) :
    π*(31/10)*(∑' i : ℕ, poissonTerm (k-1) (x*(i+1:ℕ))) < 1/10 := by
  have hk200 : 2*(k-1:ℕ) ≤ (200:ℕ) := by omega
  have hm : 2*((k-1:ℕ):ℝ) ≤ x := (show 2*((k-1:ℕ):ℝ) ≤ 200 by exact_mod_cast hk200).trans hx
  let f (i : ℕ) := poissonTerm (k-1) (x*(i+1:ℕ))
  have hf (i : ℕ) : f i ≤ (1/101:ℝ)^(i+1) := by
    simpa only [f,mul_comm x] using far_poisson_term_frequency (Nat.succ_pos i) hx hm
  have hgeo : Summable (fun i : ℕ => (1/101:ℝ)^(i+1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have hsum := (hgeo.of_nonneg_of_le (fun i => show 0 ≤ f i by dsimp [f,poissonTerm]; positivity) hf).tsum_le_tsum hf hgeo
  have hgeom : (∑' i : ℕ, (1/101:ℝ)^(i+1)) = 1/100 := by
    simp only [pow_succ,tsum_mul_right,tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/101) (by norm_num : (1/101:ℝ)<1)]
    norm_num
  rw [hgeom] at hsum
  have hPi : π*(31/10) ≤ (3.15:ℝ)*(31/10) :=
    mul_le_mul_of_nonneg_right pi_lt_d2.le (by norm_num)
  exact (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ π*(31/10))).trans_lt
    ((mul_le_mul_of_nonneg_right hPi (by norm_num : (0:ℝ) ≤ 1/100)).trans_lt (by norm_num))

#print axioms small_mid_vertical_budget
#print axioms small_far_vertical_budget
end OpenMathResearch.LongCycleExcedances
