import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

/-- Mass of an i-label load when each of n independent labels hits a
given color support with probability x. -/
def colorLoad (n i : ℕ) (x : ℝ) : ℝ :=
  x^i*(1-x)^(n-i)*(n.choose i:ℝ)

theorem color_load_nonneg (n i : ℕ) {x : ℝ} (hx : 0≤x) (hu : x≤1) :
    0≤colorLoad n i x := by
  unfold colorLoad
  exact mul_nonneg (mul_nonneg (pow_nonneg hx _) (pow_nonneg (sub_nonneg.mpr hu) _)) (by positivity)

theorem color_load_tilt (n : ℕ) (x z : ℝ) :
    ∑ i ∈ range (n+1), z^i*colorLoad n i x = (z*x+(1-x))^n := by
  rw [add_pow]
  apply sum_congr rfl
  intro i hi
  rw [mul_pow]
  unfold colorLoad
  ring

/-- A single comparison handles both tails, including x=0 and x=1. -/
theorem color_load_restricted (n k : ℕ) (s : Finset ℕ) {x z : ℝ}
    (hx : 0≤x) (hu : x≤1) (hz : 0≤z) (hs : s ⊆ range (n+1))
    (hw : ∀ i ∈ s, z^k≤z^i) :
    z^k*(∑ i ∈ s, colorLoad n i x)≤(z*x+(1-x))^n := by
  rw [mul_sum,←color_load_tilt]
  exact (sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (hw i hi) (color_load_nonneg n i hx hu))).trans
    (sum_le_sum_of_subset_of_nonneg hs (fun i _ _ => mul_nonneg (pow_nonneg hz _) (color_load_nonneg n i hx hu)))

private theorem color_load_exp_upper {v : ℝ} (hv : 0≤1+v) (n : ℕ) :
    (1+v)^n≤exp ((n:ℝ)*v) := by
  rw [exp_nat_mul]
  exact pow_le_pow_left₀ hv (by linarith [Real.add_one_le_exp v]) _

theorem color_load_lower_tail (n k : ℕ) {x : ℝ} (hx : 0≤x) (hu : x≤1)
    (hmean : (k:ℝ)≤3*(n:ℝ)*x/4) :
    ∑ i ∈ (range (n+1)).filter (· < k), colorLoad n i x ≤ exp (-(n:ℝ)*x/32) := by
  let s := (range (n+1)).filter (· < k)
  have hr := color_load_restricted n k s hx hu (z:=3/4) (by norm_num) (filter_subset _ _)
    (fun i hi => pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_of_lt (mem_filter.mp hi).2))
  have hneg := color_load_exp_upper (v := -x/4) (by linarith) n
  have htilt : (3/4:ℝ)^k*(∑ i ∈ s, colorLoad n i x)≤exp ((n:ℝ)*(-x/4)) := by
    have e : (3/4:ℝ)*x+(1-x)=1+ -x/4 := by ring
    rw [e] at hr
    exact hr.trans hneg
  have hc : (4/3:ℝ)≤exp (7/24) := by
    exact le_trans (by norm_num) (Real.quadratic_le_exp_of_nonneg (x:=7/24) (by norm_num))
  have hcp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤4/3) hc k
  rw [←exp_nat_mul] at hcp
  have he := mul_le_mul hcp htilt
    (mul_nonneg (by positivity) (sum_nonneg fun i _ => color_load_nonneg n i hx hu))
    (le_of_lt (exp_pos _))
  rw [←mul_assoc,←mul_pow,show (4/3:ℝ)*(3/4)=1 by norm_num,one_pow,one_mul,←exp_add] at he
  exact he.trans (exp_le_exp.mpr (by linarith))

theorem color_load_upper_tail (n k : ℕ) {x : ℝ} (hx : 0≤x) (hu : x≤1)
    (hmean : (n:ℝ)*x≤2*(k:ℝ)/3) :
    ∑ i ∈ (range (n+1)).filter (k ≤ ·), colorLoad n i x ≤ exp (-(k:ℝ)/15) := by
  let s := (range (n+1)).filter (k ≤ ·)
  have hr := color_load_restricted n k s hx hu (z:=3/2) (by norm_num) (filter_subset _ _)
    (fun i hi => pow_le_pow_right₀ (by norm_num) (mem_filter.mp hi).2)
  have e : (3/2:ℝ)*x+(1-x)=1+x/2 := by ring
  rw [e] at hr
  have hr' := hr.trans (color_load_exp_upper (v:=x/2) (by linarith) n)
  have hlog := Real.le_log_one_add_of_nonneg (x:=(1/2:ℝ)) (by norm_num)
  norm_num at hlog
  have hc : exp (2/5:ℝ)≤3/2 := by
    rw [←Real.exp_log (by norm_num : (0:ℝ) < 3/2)]
    apply exp_le_exp.mpr
    exact hlog
  have hcp := pow_le_pow_left₀ (le_of_lt (exp_pos _)) hc k
  rw [←exp_nat_mul] at hcp
  have hmul := (mul_le_mul_of_nonneg_right hcp (sum_nonneg (s:=s) fun i _ => color_load_nonneg n i hx hu)).trans hr'
  have h := mul_le_mul_of_nonneg_left hmul (le_of_lt (exp_pos (-((k:ℝ)*(2/5)))))
  rw [←mul_assoc,←exp_add,neg_add_cancel,exp_zero,one_mul,←exp_add] at h
  exact h.trans (exp_le_exp.mpr (by linarith))

#print axioms color_load_lower_tail
#print axioms color_load_upper_tail
end OpenMathResearch.LongCycleExcedances
