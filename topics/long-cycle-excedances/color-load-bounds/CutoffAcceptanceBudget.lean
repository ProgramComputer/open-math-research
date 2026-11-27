import ColorLoadRanges

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances.ColorAnchor
open Real

/-- The first moment over exceptionally light large orbits costs less than
1/250 of the elementary lower bound for the color-permutation cutoff. -/
theorem actual_load_lower_budget {n p k b : ℕ} (hp : 0 < p) (hb : 0 < b)
    (hsize : 200*p ≤ n) (hcut : 4*k*p ≤ 3*n*b) :
    let D : ℝ := (p.factorial:ℝ)*(p:ℝ)^n
    (Nat.card (BaselinePairs n p b):ℝ)/D-(1/250:ℝ)/(2*(b:ℝ)-1) <
      (Nat.card (Accepted n p k):ℝ)/D := by
  dsimp only
  have hpp : (0:ℝ) < p := by positivity
  have hn : 0 < n := by omega
  have hsize' : 200*(p:ℝ)≤(n:ℝ) := by exact_mod_cast hsize
  have hcut' : 4*(k:ℝ)*p ≤ 3*n*b := by exact_mod_cast hcut
  have hmean (j : ℕ) (hbj : b ≤ j) (_ : j ≤ p) : (k:ℝ)≤3*n*((j:ℝ)/p)/4 := by
    have hj : (b:ℝ)≤j := by exact_mod_cast hbj
    rw [←mul_div_assoc,div_div]
    apply (le_div_iff₀ (mul_pos hpp (by norm_num))).2
    nlinarith [mul_nonneg (show 0≤(n:ℝ) by positivity) (sub_nonneg.mpr hj)]
  have hsmall : exp (-(n:ℝ)/(32*(p:ℝ)))≤exp (-(25/4):ℝ) := by
    apply exp_le_exp.mpr
    apply (div_le_iff₀ (by positivity)).2
    linarith
  have hgap := (color_long_load_budget n p k b hp hn hb hmean).trans_lt
    (color_load_large_orbit_budget (b:=(b:ℝ)) (exp_pos _).le hsmall (by exact_mod_cast hb))
  have hh := (actual_color_probability_comparison n p k b hp).1
  linarith

/-- A cutoff chosen just above 2kp/(3n) loses at most 9/(1000a) in
the upper comparison, where a=kp/n. -/
theorem actual_load_upper_budget {n p k b : ℕ} (hp : 0 < p) (hb : 0 < b)
    (hsize : 100*p ≤ n) (hlarge : 3*n ≤ 2*k*p) (hcut : 3*n*(b-1) ≤ 2*k*p) :
    let a := (k:ℝ)*p/n
    let D : ℝ := (p.factorial:ℝ)*(p:ℝ)^n
    (Nat.card (Accepted n p k):ℝ)/D ≤ (Nat.card (BaselinePairs n p b):ℝ)/D + (9/1000:ℝ)/a := by
  dsimp only
  let a := (k:ℝ)*p/n
  let μ := (n:ℝ)/p
  have hpp : (0:ℝ) < p := by positivity
  have hn : 0 < n := by omega
  have hnp : (0:ℝ) < n := by positivity
  have hlarge' : 3*(n:ℝ) ≤ 2*(k:ℝ)*p := by exact_mod_cast hlarge
  have hcut' : 3*(n:ℝ)*((b-1:ℕ):ℝ) ≤ 2*(k:ℝ)*p := by exact_mod_cast hcut
  have hμ : 100≤μ := (le_div_iff₀ hpp).2 (by exact_mod_cast hsize)
  have ha : 3/2≤a := (le_div_iff₀ hnp).2 (by linarith)
  have hap : 0 < a := by linarith
  have hprod : a*μ=(k:ℝ) := by dsimp [a,μ]; field_simp
  have hmean (j : ℕ) (_ : 0 < j) (hj : j < b) (_ : j ≤ p) : (n:ℝ)*((j:ℝ)/p)≤2*k/3 := by
    have ht : (j:ℝ)≤((b-1:ℕ):ℝ) := by exact_mod_cast (show j≤b-1 by omega)
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hpp).2
    nlinarith [mul_nonneg hnp.le (sub_nonneg.mpr ht)]
  have hc : ((b-1:ℕ):ℝ)≤(2/3:ℝ)*a := by
    change _ ≤ (2/3:ℝ)*((k:ℝ)*p/n)
    rw [←mul_div_assoc]
    apply (le_div_iff₀ hnp).2
    linarith
  have he := color_load_small_orbit_budget ha hμ
  rw [hprod,←neg_div] at he
  have ht := color_short_load_budget n p k b hp hmean
  have hnew : expectedColorMarks n p (fun j i => j < b ∧ k ≤ i) ≤ (9/1000:ℝ)/a := by
    apply (le_div_iff₀ hap).2
    have hh := (mul_le_mul_of_nonneg_right ht hap.le).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (exp_pos _).le) hap.le)
    nlinarith only [hh,he]
  exact (actual_color_probability_comparison n p k b hp).2.trans (add_le_add_left hnew _)

#print axioms actual_load_lower_budget
#print axioms actual_load_upper_budget
end OpenMathResearch.LongCycleExcedances.ColorAnchor
