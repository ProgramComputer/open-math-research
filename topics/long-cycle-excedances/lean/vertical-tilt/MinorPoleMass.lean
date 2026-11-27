import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances

open Real Finset

private theorem eighteen_le_exp : (18:ℝ) ≤ exp (74/25) := by
  refine le_trans ?_ (Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 74/25 by norm_num) 7)
  norm_num [sum_range_succ, Nat.factorial]

private theorem odd_le_three_pow (j : ℕ) : (2:ℝ)*j+1 ≤ 3^j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [pow_succ, Nat.cast_succ]
    nlinarith only [ih,Nat.cast_nonneg (α := ℝ) j]

/-- The joint radial and log-tilt exponent gives a geometric budget for
the weighted contribution from each positive nonprincipal odd pole. -/
theorem weighted_odd_mode_bound {j : ℕ} (hj : 1 ≤ j) :
    let p : ℝ := 2*j+1
    p*exp (-(49/100)*(p^2-1)+(12/25)*(p-1)) ≤ (1/6:ℝ)^j := by
  let p : ℝ := 2*j+1
  change p*exp _ ≤ _
  have hj' : (1:ℝ) ≤ j := by exact_mod_cast hj
  have hquad : (j:ℝ) ≤ (j:ℝ)^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hj') (Nat.cast_nonneg (α := ℝ) j)]
  have hearg : -(49/100)*(p^2-1)+(12/25)*(p-1) ≤ (j:ℝ)*(-(74/25)) := by
    dsimp only [p]
    nlinarith only [hquad]
  have hex : exp (-(74/25:ℝ)) ≤ 1/18 := by
    rw [exp_neg,←one_div]
    exact one_div_le_one_div_of_le (by norm_num) eighteen_le_exp
  have he := exp_le_exp.mpr hearg
  rw [exp_nat_mul] at he
  have h := mul_le_mul (odd_le_three_pow j)
    (he.trans (pow_le_pow_left₀ (exp_pos _).le hex j)) (exp_pos _).le (by positivity : (0:ℝ) ≤ 3^j)
  rw [←mul_pow] at h
  rw [show (3:ℝ)*(1/18)=1/6 by norm_num] at h
  simpa only [p] using h

theorem weighted_minor_poles_le_fifth (s : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ i ∈ s, f i ≤
      let p : ℝ := 2*(i+1:ℕ)+1
      p*exp (-(49/100)*(p^2-1)+(12/25)*(p-1))) :
    ∑ i ∈ s, f i ≤ 1/5 := by
  have hs : Summable fun i : ℕ => (1/6:ℝ)^(i+1) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have hgeo : (∑' i : ℕ, (1/6:ℝ)^(i+1)) = 1/5 := by
    simp only [pow_succ,tsum_mul_right,tsum_geometric_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/6) (by norm_num : (1/6:ℝ)<1)]
    norm_num
  apply (sum_le_sum (g := fun i => (1/6:ℝ)^(i+1))
    (fun i hi => (hf i hi).trans (weighted_odd_mode_bound (Nat.succ_pos i)))).trans
  exact (hs.sum_le_tsum s (fun i _ => by positivity)).trans hgeo.le

#print axioms weighted_odd_mode_bound
#print axioms weighted_minor_poles_le_fifth
end OpenMathResearch.LongCycleExcedances
