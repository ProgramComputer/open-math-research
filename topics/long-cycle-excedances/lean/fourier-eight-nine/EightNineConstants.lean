import SmallCutoffPoisson
import HighBandConstants

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

theorem poisson_prefix_eight {x : ℝ} (hx : 0 ≤ x) (k : ℕ) (hm : (2:ℝ)*k ≤ x) :
    (∑ i ∈ range (k-1), x^i/(i.factorial:ℝ)) ≤ exp ((17/20)*x) := by
  have h : (2:ℝ) ≤ exp (7/10) := by
    refine le_trans ?_ (sum_le_exp_of_nonneg (show (0:ℝ) ≤ 7/10 by norm_num) 4)
    norm_num [sum_range_succ,Nat.factorial]
  convert poisson_lower_tilt_at hx (show (1:ℝ) ≤ 2 by norm_num)
    (show (0:ℝ) ≤ 7/10 by norm_num) h k hm using 1 <;> norm_num

theorem high_band_eight_budget {k t : ℝ} (hk : 8 ≤ k) (hu : k ≤ 9) (ht : 5 ≤ t) :
    let q : ℝ := 101/100
    let d : ℝ := 78/1000
    let split : ℝ := 2
    let decay : ℝ := 3/20
    2*q*split*exp ((d+q)*split) + q*split*exp (d*split) +
      2*q/(k*decay-(d+q)) + q/(k*decay-d) +
      2*((k/(2*t))*exp (-k/6) + 2/(1-d)) < 65 := by
  have h1 := div_le_div_of_nonneg_left (show (0:ℝ) ≤ 2*(101/100:ℝ) by norm_num)
    (show (0:ℝ) < 8*(3/20)-(78/1000+101/100) by norm_num)
    (show 8*(3/20)-(78/1000+101/100) ≤ k*(3/20)-(78/1000+101/100) by linarith)
  have h2 := div_le_div_of_nonneg_left (show (0:ℝ) ≤ 101/100 by norm_num)
    (show (0:ℝ) < 8*(3/20)-78/1000 by norm_num)
    (show 8*(3/20)-78/1000 ≤ k*(3/20)-78/1000 by linarith)
  have h3 : (k/(2*t))*exp (-k/6) ≤ 9/10 := by
    have hden : (10:ℝ) ≤ 2*t := by linarith
    have hp := div_le_div_of_nonneg_left (show 0 ≤ k by linarith) (by norm_num : (0:ℝ)<10) hden
    have hres : k/(2*t) ≤ 9/10 := hp.trans (by linarith)
    exact (mul_le_of_le_one_right (by positivity) (exp_le_one_iff.mpr (by linarith))).trans hres
  have hex : exp (272/375:ℝ) ≤ 52/25 := by
    have h := exp_bound' (x:=272/375) (by norm_num) (by norm_num) (n:=8) (by decide)
    norm_num [sum_range_succ,Nat.factorial] at h
    linarith only [h]
  have he : exp (272/125:ℝ) ≤ 9 := by
    rw [show (272/125:ℝ) = (3:ℕ)*(272/375) by norm_num, exp_nat_mul]
    exact (pow_le_pow_left₀ (exp_pos _).le hex 3).trans (by norm_num)
  have hf : exp (39/250:ℝ) ≤ 6/5 := by
    have h := exp_bound' (x:=39/250) (by norm_num) (by norm_num) (n:=5) (by decide)
    norm_num [sum_range_succ,Nat.factorial] at h
    linarith only [h]
  norm_num at h1 h2 he hf ⊢
  linarith only [h1,h2,h3,he,hf]

#print axioms poisson_prefix_eight
#print axioms high_band_eight_budget
end OpenMathResearch.LongCycleExcedances
