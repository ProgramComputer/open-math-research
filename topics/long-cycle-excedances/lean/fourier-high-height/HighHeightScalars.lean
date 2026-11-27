import PoissonTilts
import Mathlib.Data.Real.Pi.Bounds

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

theorem high_height_geometry {k s r : ℝ} (hk : 100 ≤ k) (hs : 0 < s)
    (hr : 0 ≤ r) (hhigh : 16*k < s^2) (hcircle : r^2 = s^2+π^2) :
    s ≤ r ∧ r-s < (31/100)*s/k ∧ r < (251/250)*s ∧
      (1+1/k)*r-s < (657/500)*s/k ∧
      (69/100)*s/k < s-(1-1/k)*r ∧ 1 < (1-1/k)*r := by
  have hk0 : 0 < k := by linarith
  have hsr : s ≤ r := by nlinarith [sq_nonneg π]
  have hp4 := pi_lt_d4
  have hpi : π^2 < (248/25:ℝ) := by
    nlinarith [mul_pos (sub_pos.mpr hp4) (add_pos pi_pos (by norm_num : (0:ℝ)<3.1416))]
  have hb : (r-s)*(2*s) ≤ π^2 := by
    nlinarith only [hcircle, sq_nonneg (r-s)]
  have hcore : (r-s)*k < (31/100)*s := by
    apply lt_of_mul_lt_mul_right ?_ (by linarith : 0 ≤ 2*s)
    nlinarith only [mul_le_mul_of_nonneg_right hb hk0.le,
      mul_lt_mul_of_pos_right hpi hk0, hhigh]
  have hd := (lt_div_iff₀ hk0).mpr hcore
  have hq : r < (251/250)*s := by
    have hh : (31/100:ℝ)*s < ((1/250:ℝ)*s)*k := by
      nlinarith only [mul_le_mul_of_nonneg_left hk hs.le, hs]
    have hout := (lt_div_iff₀ hk0).mp hd
    have hdiff : r-s < (1/250:ℝ)*s :=
      lt_of_mul_lt_mul_right (hout.trans hh) hk0.le
    linarith
  have hd' : r-s < (31/100)*(s/k) := by simpa only [mul_div_assoc] using hd
  have hR : (1+1/k)*r-s < (657/500)*s/k := by
    have hq' : r/k < (251/250)*(s/k) := by
      simpa only [mul_div_assoc] using (div_lt_div_iff_of_pos_right hk0).mpr hq
    rw [show (1+1/k)*r-s = r-s+r/k by ring, mul_div_assoc]
    linarith
  have hgap : (69/100)*s/k < s-(1-1/k)*r := by
    have hsr' := (div_le_div_iff_of_pos_right hk0).mpr hsr
    rw [show s-(1-1/k)*r = r/k-(r-s) by ring, mul_div_assoc]
    linarith
  have hs40 : 40 < s := by nlinarith [mul_nonneg hs.le (show (0:ℝ)≤40 by norm_num)]
  have hcoef : (99/100:ℝ) ≤ 1-1/k := by
    have hinv : 1/k ≤ (1/100:ℝ) := by
      apply (div_le_iff₀ hk0).mpr
      linarith
    linarith
  have hbig := mul_le_mul hcoef (show 40 ≤ r by linarith) (by norm_num : (0:ℝ) ≤ 40) (by linarith : 0 ≤ 1-1/k)
  exact ⟨hsr, hd, hq,hR,hgap,by linarith⟩

private theorem exp_outer : exp (657/400) < 21/4 := by
  have h := exp_bound' (x:=657/800) (by norm_num) (by norm_num) (n:=6) (by decide)
  have hh : exp (657/800) ≤ 229/100 := by
    apply h.trans
    norm_num [sum_range_succ, Nat.factorial]
  rw [show (657/400:ℝ)=657/800+657/800 by norm_num, exp_add]
  nlinarith [mul_le_mul hh hh (exp_pos _).le (show (0:ℝ) ≤ 229/100 by norm_num)]

private theorem exp_inner : exp (31/80) < 3/2 := by
  have h := exp_bound' (x:=31/80) (by norm_num) (by norm_num) (n:=5) (by decide)
  apply h.trans_lt
  norm_num [sum_range_succ,Nat.factorial]

theorem high_height_cost_budget {k : ℝ} (hk : 100 ≤ k) :
    2*(251/250)* (5/4) * exp (657/400) +
    (251/250)*(5/4)*exp (31/80) +
    (2*(251/250))/(k/50-657/500) +
    (251/250)/(k/50-31/100) + 2*((1/1000)+2/(69/100)) < 25 := by
  have h₁ : 0 < k/50-657/500 := by linarith
  have h₂ : 0 < k/50-31/100 := by linarith
  have h₃ : (2*(251/250:ℝ))/(k/50-657/500) ≤ 3 := by
    apply (div_le_iff₀ h₁).mpr
    linarith
  have h₄ : (251/250:ℝ)/(k/50-31/100) ≤ 3/5 := by
    apply (div_le_iff₀ h₂).mpr
    linarith
  linarith [exp_outer, exp_inner]

theorem high_height_exp_reserve {k : ℝ} (hk : 100 ≤ k) :
    k*exp (-k/6) ≤ 1/1000 := by
  rw [show -k/6=-(k/6) by ring, exp_neg]
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (exp_pos _)).mpr
  have hpos : (0:ℝ)≤k/6 := by linarith
  have h := Real.pow_div_factorial_le_exp (k/6) hpos 8
  have hk7 : (100/6:ℝ)^7 ≤ (k/6)^7 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) _
  have ht := mul_le_mul_of_nonneg_left hk7 hpos
  norm_num [Nat.factorial] at h
  have hc : (1000:ℝ)*k ≤ (k/6)^8/40320 := by
    have h8 : (k/6)^8 = (k/6)*(k/6)^7 := by ring
    rw [h8]
    calc
      _ ≤ ((k/6)*(100/6:ℝ)^7)/40320 := by
        have hc : (1000:ℝ) ≤ ((100/6:ℝ)^7)/(6*40320) := by norm_num
        nlinarith only [mul_le_mul_of_nonneg_right hc (show 0 ≤ k by linarith)]
      _ ≤ _ := div_le_div_of_nonneg_right ht (by norm_num)
  linarith only [hc.trans h]

#print axioms high_height_geometry
#print axioms high_height_cost_budget
#print axioms high_height_exp_reserve
end OpenMathResearch.LongCycleExcedances
