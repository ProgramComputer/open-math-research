import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Ring

noncomputable section
namespace OpenMathResearch.LongCycleExcedances

theorem norm_negative_exp_lt_one {x : ℝ} (hx : 0 < x) :
    ‖-Real.exp (-x)‖ < 1 := by
  rw [norm_neg, Real.norm_of_nonneg (Real.exp_nonneg _), Real.exp_lt_one_iff]
  exact neg_lt_zero.mpr hx

/-- Lift a real alternating moment to a complex sum starting at one.
The order condition makes the discarded degree-zero index vanish. -/
theorem complex_hasSum_discrete_moment {x M : ℝ} {d : ℕ} (hx : 0 < x) (hd : 2 ≤ d)
    (hM : M = ∑' h : ℕ, (-1 : ℝ)^h * h^(d-1) * Real.exp (-(x*(h:ℝ)))) :
    HasSum (fun i : ℕ => ((-Real.exp (-x):ℝ):ℂ)^(i+1) * (((i+1:ℕ):ℂ)^(d-1))) (M:ℂ) := by
  let f (h : ℕ) : ℝ := (h:ℝ)^(d-1) * (-Real.exp (-x))^h
  have hs : Summable f := summable_pow_mul_geometric_of_norm_lt_one _ (norm_negative_exp_lt_one hx)
  have hf (h : ℕ) : f h = (-1:ℝ)^h * h^(d-1) * Real.exp (-(x*(h:ℝ))) := by
    dsimp only [f]
    rw [show -(x*(h:ℝ))=(h:ℝ)*(-x) by ring, Real.exp_nat_mul,
      show -Real.exp (-x)=(-1)*Real.exp (-x) by ring, mul_pow]
    ring
  have he : (∑' h : ℕ, f h) = M := (tsum_congr hf).trans hM.symm
  have h := he ▸ hs.hasSum
  have hzero : f 0 = 0 := by simp [f, zero_pow (show d-1 ≠ 0 by omega)]
  have hshift := (hasSum_nat_add_iff' (f := f) 1).mpr h
  rw [Finset.sum_range_one, hzero, sub_zero] at hshift
  simpa only [f, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast, mul_comm] using
    Complex.hasSum_ofReal.mpr hshift

theorem shifted_complex_geometric {q : ℂ} (h : ‖q‖ < 1) :
    HasSum (fun i : ℕ => q^(i+1)) (q/(1-q)) := by
  simpa only [pow_succ',div_eq_mul_inv] using (hasSum_geometric_of_norm_lt_one h).mul_left q

theorem complex_exp_negative_odd_pole (x : ℝ) (l : ℤ) :
    Complex.exp (-((x:ℂ)+(2*(l:ℂ)+1)*Real.pi*Complex.I)) =
      ((-Real.exp (-x):ℝ):ℂ) := by
  have he : -((x:ℂ)+(2*(l:ℂ)+1)*Real.pi*Complex.I) =
      (-(x:ℂ) + (((-l:ℤ):ℂ))*(2*Real.pi*Complex.I))-(Real.pi:ℂ)*Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_sub_pi_mul_I, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
    ← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Complex.ofReal_neg]

#print axioms complex_hasSum_discrete_moment
#print axioms shifted_complex_geometric
#print axioms complex_exp_negative_odd_pole
end OpenMathResearch.LongCycleExcedances
