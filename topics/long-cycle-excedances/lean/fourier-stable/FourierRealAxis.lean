import LongCycleBounds.PartialFractions
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open scoped Real

/-- Eulerian squared-pole identity to the left of the pole line.
The signed odd-pole expansion is due to Bowen Zuo. -/
theorem fourier_squared_poles_real_axis (s x : ℝ) (hx : x < s) :
    (∑' l : ℤ, 1 / ((s : ℂ) + (2 * (l : ℂ) + 1) * π * Complex.I - (x : ℂ)) ^ 2) =
      -Complex.exp ((x : ℂ) - (s : ℂ)) / (1 + Complex.exp ((x : ℂ) - (s : ℂ))) ^ 2 := by
  have he : ‖-Complex.exp ((x : ℂ) - (s : ℂ))‖ < 1 := by
    rw [norm_neg, Complex.norm_exp, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re]
    exact Real.exp_lt_one_iff.mpr (sub_neg.mpr hx)
  have hexp : ((Real.exp (-(s - x)) : ℝ) : ℂ) = Complex.exp ((x : ℂ) - (s : ℂ)) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have h := LongCycleBounds.oddPoleSum_eq_powerSeries_of_pos 1 (by decide) (s - x) (sub_pos.mpr hx)
  rw [hexp] at h
  simp only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one] at h
  calc
    _ = LongCycleBounds.oddPoleSum 2 (s - x) := by
      unfold LongCycleBounds.oddPoleSum
      apply tsum_congr
      intro l
      rw [Complex.ofReal_sub]
      congr 2
      ring
    _ = _ := by
      rw [h, tsum_coe_mul_geometric_of_norm_lt_one he, sub_neg_eq_add]

#print axioms fourier_squared_poles_real_axis
end OpenMathResearch.LongCycleExcedances
