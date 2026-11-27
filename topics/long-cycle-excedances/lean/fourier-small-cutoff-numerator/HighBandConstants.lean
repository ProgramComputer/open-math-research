import HighBandNumerator
import HighHeightScalars

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

theorem high_band_geometry_at {k s r b d q K : ℝ} (hK : 0 < K) (hk : K ≤ k)
    (hs : 0 < s) (hr : 0 ≤ r) (hhigh : b^2*k < s^2)
    (hcircle : r^2 = s^2+π^2) (hd : 0 < d)
    (hsquare : (3.1416:ℝ)^2 ≤ 2*d*b^2) (hq : 1+d/K ≤ q) :
    s ≤ r ∧ r-s ≤ d*s/k ∧ r ≤ q*s := by
  have hkr := hK.trans_le hk
  have hsr : s ≤ r := by nlinarith [sq_nonneg π]
  have hpi := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d4.le 2
  have hbound : (r-s)*(2*s) ≤ π^2 := by
    nlinarith only [hcircle,sq_nonneg (r-s)]
  have hdiff : (r-s)*k ≤ d*s := by
    apply le_of_mul_le_mul_right _ (by linarith : 0 < 2*s)
    nlinarith only [mul_le_mul_of_nonneg_right hbound hkr.le,
      mul_le_mul_of_nonneg_right (hpi.trans hsquare) hkr.le,
      mul_le_mul_of_nonneg_left hhigh.le (show 0 ≤ 2*d by positivity)]
  have hd' : r-s ≤ d*s/k := (le_div_iff₀ hkr).mpr hdiff
  refine ⟨hsr,hd',?_⟩
  have hm := div_le_div_of_nonneg_left hd.le hK hk
  have h' := mul_le_mul_of_nonneg_right (show 1+d/k ≤ q by linarith) hs.le
  linarith only [hd', h', show (1+d/k)*s = s+d*s/k by ring]

private theorem exp_wide_fifty : exp (9219/5000 : ℝ) ≤ (63/25:ℝ)^2 := by
  have h := exp_bound' (x:=9219/10000) (by norm_num) (by norm_num) (n:=8) (by decide)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  have h' : exp (9219/10000:ℝ) ≤ 63/25 := by linarith only [h]
  rw [show (9219/5000:ℝ)=9219/10000+9219/10000 by norm_num,exp_add,←pow_two]
  exact pow_le_pow_left₀ (exp_pos _).le h' 2

private theorem exp_main_fifty : exp (217/500 : ℝ) ≤ 31/20 := by
  have h := exp_bound' (x:=217/500) (by norm_num) (by norm_num) (n:=6) (by decide)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  linarith only [h]

private theorem exp_wide_ten : exp (543/250 : ℝ) ≤ (207/100:ℝ)^3 := by
  have h := exp_bound' (x:=181/250) (by norm_num) (by norm_num) (n:=8) (by decide)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  have h' : exp (181/250:ℝ) ≤ 207/100 := by linarith only [h]
  rw [show (543/250:ℝ) = (3:ℕ)*(181/250) by norm_num, exp_nat_mul]
  exact pow_le_pow_left₀ (exp_pos _).le h' 3

private theorem exp_main_ten : exp (39/250 : ℝ) ≤ 59/50 := by
  have h := exp_bound' (x:=39/250) (by norm_num) (by norm_num) (n:=5) (by decide)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  linarith only [h]

private theorem reserve_fifty {k t : ℝ} (hk : 50 ≤ k) (hu : k ≤ 99)
    (ht : 1 ≤ t) : (k/(2*t))*exp (-k/6) ≤ 1/10 := by
  have hk0 : 0 ≤ k := by linarith
  have hE : (500:ℝ) ≤ exp (25/3) := by
    apply le_trans _ (exp_le_exp.mpr (show (8:ℝ) ≤ 25/3 by norm_num))
    rw [show (8:ℝ) = (8:ℕ)*1 by norm_num, exp_nat_mul]
    have h : (27/10:ℝ) ≤ exp 1 := by linarith only [Real.exp_one_gt_d9]
    exact (by norm_num : (500:ℝ) ≤ (27/10)^8).trans
      (pow_le_pow_left₀ (by norm_num) h 8)
  have hx : exp (-k/6) ≤ 1/500 := by
    calc
      _ ≤ exp (-(25/3:ℝ)) := exp_le_exp.mpr (by linarith)
      _ ≤ _ := by rw [exp_neg,←one_div]; exact one_div_le_one_div_of_le (by norm_num) hE
  have hy : k/(2*t) ≤ 99/2 := by
    have h := div_le_div_of_nonneg_left hk0 (show (0:ℝ)<2 by norm_num)
      (show 2 ≤ 2*t by linarith)
    exact h.trans (div_le_div_of_nonneg_right hu (by norm_num))
  exact (mul_le_mul hy hx (exp_pos _).le (by norm_num)).trans (by norm_num)

private theorem reserve_ten {k t : ℝ} (hk : 10 ≤ k) (hu : k ≤ 49)
    (ht : 5 ≤ t) : (k/(2*t))*exp (-k/6) ≤ 1 := by
  have hk0 : 0 ≤ k := by linarith
  have hE : (5:ℝ) ≤ exp (5/3) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 5/3 by norm_num) 5)
    norm_num [Finset.sum_range_succ,Nat.factorial]
  have hx : exp (-k/6) ≤ 1/5 := by
    calc
      _ ≤ exp (-(5/3:ℝ)) := exp_le_exp.mpr (by linarith)
      _ ≤ _ := by rw [exp_neg,←one_div]; exact one_div_le_one_div_of_le (by norm_num) hE
  have hy : k/(2*t) ≤ 49/10 := by
    have h := div_le_div_of_nonneg_left hk0 (show (0:ℝ)<10 by norm_num)
      (show 10 ≤ 2*t by linarith)
    exact h.trans (div_le_div_of_nonneg_right hu (by norm_num))
  exact (mul_le_mul hy hx (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem high_band_fifty_budget {k t : ℝ} (hk : 50 ≤ k) (hu : k ≤ 99) (ht : 1 ≤ t) :
    let q : ℝ := 1007/1000
    let d : ℝ := 31/100
    let split : ℝ := 7/5
    let decay : ℝ := 9/200
    2*q*split*exp ((d+q)*split) + q*split*exp (d*split) +
      2*q/(k*decay-(d+q)) + q/(k*decay-d) +
      2*((k/(2*t))*exp (-k/6) + 2/(1-d)) < 32 := by
  have h1 := div_le_div_of_nonneg_left (show (0:ℝ) ≤ 2*(1007/1000:ℝ) by norm_num)
    (show (0:ℝ) < 50*(9/200)-(31/100+1007/1000) by norm_num)
    (show 50*(9/200)-(31/100+1007/1000) ≤ k*(9/200)-(31/100+1007/1000) by linarith)
  have h2 := div_le_div_of_nonneg_left (show (0:ℝ) ≤ 1007/1000 by norm_num)
    (show (0:ℝ) < 50*(9/200)-31/100 by norm_num)
    (show 50*(9/200)-31/100 ≤ k*(9/200)-31/100 by linarith)
  have h3 := reserve_fifty hk hu ht
  have he := exp_wide_fifty
  have hf := exp_main_fifty
  norm_num at h1 h2 he hf ⊢
  linarith only [h1,h2,h3,he,hf]

theorem high_band_ten_budget {k t : ℝ} (hk : 10 ≤ k) (hu : k ≤ 49) (ht : 5 ≤ t) :
    let q : ℝ := 1008/1000
    let d : ℝ := 78/1000
    let split : ℝ := 2
    let decay : ℝ := 1/8
    2*q*split*exp ((d+q)*split) + q*split*exp (d*split) +
      2*q/(k*decay-(d+q)) + q/(k*decay-d) +
      2*((k/(2*t))*exp (-k/6) + 2/(1-d)) < 60 := by
  have h1 := div_le_div_of_nonneg_left (show (0:ℝ) ≤ 2*(1008/1000:ℝ) by norm_num)
    (show (0:ℝ) < 10*(1/8)-(78/1000+1008/1000) by norm_num)
    (show 10*(1/8)-(78/1000+1008/1000) ≤ k*(1/8)-(78/1000+1008/1000) by linarith)
  have h2 := div_le_div_of_nonneg_left (show (0:ℝ) ≤ 1008/1000 by norm_num)
    (show (0:ℝ) < 10*(1/8)-78/1000 by norm_num)
    (show 10*(1/8)-78/1000 ≤ k*(1/8)-78/1000 by linarith)
  have h3 := reserve_ten hk hu ht
  have he := exp_wide_ten
  have hf := exp_main_ten
  norm_num at h1 h2 he hf ⊢
  linarith only [h1,h2,h3,he,hf]

#print axioms high_band_geometry_at
#print axioms high_band_fifty_budget
#print axioms high_band_ten_budget
end OpenMathResearch.LongCycleExcedances
