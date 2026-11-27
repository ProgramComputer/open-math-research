import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

/-- The union over short color orbits only needs the number of possible
lengths. Bounding this number by 2a/3 removes the harmonic/log-size term. -/
theorem color_load_small_orbit_budget {a μ : ℝ} (ha : 3/2 ≤ a) (hm : 100 ≤ μ) :
    (2/3:ℝ)*a^2*exp (-(a*μ/15)) ≤ 9/1000 := by
  let x := a*μ/15
  have hap : 0 < a := by linarith
  have hm' : 0≤μ := by linarith
  have hx : (20/3)*a≤x := by dsimp [x]; nlinarith [mul_nonneg hap.le (sub_nonneg.mpr hm)]
  have hxp : 0 ≤ x := by dsimp [x]; positivity
  have hc : x^3/6 ≤ exp x := by
    have h := Real.sum_le_exp_of_nonneg hxp 4
    norm_num [sum_range_succ,Nat.factorial] at h
    nlinarith [sq_nonneg x]
  have cube := pow_le_pow_left₀ (by positivity : 0≤(20/3:ℝ)*a) hx 3
  change (2/3:ℝ)*a^2*exp (-x) ≤ _
  rw [exp_neg,←div_eq_mul_inv]
  apply (div_le_iff₀ (exp_pos x)).2
  nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.mpr ha)]

theorem color_load_geom_small : exp (-(25/4):ℝ) < 1/501 := by
  rw [Real.exp_neg,one_div,inv_lt_inv₀ (exp_pos _) (by norm_num : (0:ℝ) < 501)]
  have h1 : (2718/1000:ℝ) < exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) h1.le 6
  have he : exp (25/4:ℝ)=exp 1^6*exp (1/4) := by
    rw [←Real.exp_nat_mul,←exp_add]; congr 1; norm_num
  rw [he]
  have hq : (5/4:ℝ)≤exp (1/4) := by linarith [Real.add_one_le_exp (1/4)]
  have HH := mul_le_mul hp hq (by norm_num) (by positivity)
  exact lt_of_lt_of_le (by norm_num) HH

/-- When the mean per color is at least 200, the loss from all large
marked orbits is less than 1/250 of the survival lower bound 1/(2b-1). -/
theorem color_load_large_orbit_budget {r : ℝ} (hr : 0≤r) (hsmall : r≤exp (-(25/4):ℝ))
    {b : ℝ} (hb : 1≤b) :
    (1/b)*(r/(1-r)) < (1/250:ℝ)/(2*b-1) := by
  have h := hsmall.trans_lt color_load_geom_small
  have hb0 : 0 < b := by linarith
  have hx : 0 < 1-r := by linarith
  have hd : 0 < 2*b-1 := by linarith
  apply (lt_div_iff₀ hd).2
  rw [show (1/b)*(r/(1-r))*(2*b-1)=r*(2*b-1)/(b*(1-r)) by field_simp [hb0.ne', hx.ne']]
  apply (div_lt_iff₀ (mul_pos hb0 hx)).2
  nlinarith [mul_pos hb0 (show 0 < 1-501*r by linarith)]

/-- Rank-scaled error of removing surplus bars. At n≥10000 the right side
is at most 3/4000. The estimate uses only the fifth exponential moment. -/
theorem color_load_transform_budget {n p b : ℝ} (hn : 0 < n) (hp : 0 < p)
    (hbp : b≤p) (hscale : 4*p^2≤n) :
    (2*b-1)*(2*n*exp (-(n/p))) ≤ 15/(2*n) := by
  have hterm : (n/p)^5/120 ≤ exp (n/p) := by
    have x := Real.sum_le_exp_of_nonneg (div_nonneg hn.le hp.le) 6
    have h := Finset.single_le_sum (s:=range 6) (f:=fun i : ℕ => (n/p)^i/(i.factorial:ℝ))
      (fun i _ => (by positivity : 0≤(n/p)^i/(i.factorial:ℝ))) (show 5 ∈ range 6 by decide)
    norm_num [Nat.factorial] at h
    exact h.trans x
  have hcube := pow_le_pow_left₀ (by positivity : 0≤4*p^2) hscale 3
  have hpow : n^5 ≤ 120*(exp (n/p))*p^5 := by
    rw [div_pow] at hterm
    have hmul := (div_le_iff₀ (show 0 < (120:ℝ) by norm_num)).1 hterm
    have hm := (div_le_iff₀ (pow_pos hp 5)).1 hmul
    linarith
  have hsmall : 8*p*n^2 ≤ 15*exp (n/p) := by
    apply (mul_le_mul_iff_left₀ (pow_pos hp 5)).1
    nlinarith [mul_le_mul_of_nonneg_right hcube (sq_nonneg n)]
  rw [exp_neg]
  apply (le_div_iff₀ (by positivity : 0 < 2*n)).2
  rw [show (2*b-1)*(2*n*(exp (n/p))⁻¹)*(2*n)=((2*b-1)*4*n^2)/exp (n/p) by ring]
  apply (div_le_iff₀ (exp_pos _)).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hbp) (sq_nonneg n)]

#print axioms color_load_transform_budget
#print axioms color_load_small_orbit_budget
#print axioms color_load_large_orbit_budget
end OpenMathResearch.LongCycleExcedances
