import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OpenMathResearch.LongCycleExcedances
open Real
private theorem parity_square (j : ℕ) : ((-1:ℝ)^j)^2 = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

/-- A phase within half a radian of an integral multiple of π has a cosine
of known sign and magnitude at least 7/8. -/
theorem signed_cos_grid {v : ℝ} (j : ℕ) (h : |v - j*π| ≤ 1/2) :
    7/8 ≤ (-1:ℝ)^j * cos v := by
  have hb := abs_le.mp h
  have small : (v-j*π)^2 ≤ (1/2:ℝ)^2 := by
    nlinarith [mul_nonneg (by linarith [hb.1] : 0 ≤ (1/2:ℝ)+(v-j*π))
      (by linarith [hb.2] : 0 ≤ (1/2:ℝ)-(v-j*π))]
  have e : cos v = (-1:ℝ)^j * cos (v-j*π) := by
    simpa only [sub_add_cancel] using cos_add_nat_mul_pi (v-j*π) j
  rw [e, ← mul_assoc, ← sq, parity_square, one_mul]
  linarith [one_sub_sq_div_two_le_cos (x := v-j*π)]

/-- At a near-zero cosine in a slightly enlarged cell, the sine has the
orientation of the unperturbed cell. -/
theorem signed_sin_grid_cell {v s : ℝ} (j : ℕ)
    (lo : j*π ≤ s) (hi : s ≤ (j+1:ℕ)*π) (hvs : |v-s| ≤ 1/2)
    (hc : |cos v| ≤ 1/6) : 0 < (-1:ℝ)^j * sin v := by
  have near := abs_le.mp hvs
  have outside (m : ℕ) (hm : |v - m*π| ≤ 1/2) : False := by
    have hg := signed_cos_grid m hm
    have hu := le_abs_self ((-1:ℝ)^m * cos v)
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at hu
    linarith
  have hl : j*π < v := by
    by_contra! bad
    exact outside j (abs_le.mpr ⟨by linarith [near.1], by linarith⟩)
  have hr : v < (j+1:ℕ)*π := by
    by_contra! bad
    exact outside (j+1) (abs_le.mpr ⟨by linarith, by linarith [near.2]⟩)
  have hs := sin_pos_of_pos_of_lt_pi (sub_pos.mpr hl)
    (show v-j*π < π by push_cast at hr; linarith)
  have e : sin v = (-1:ℝ)^j * sin (v-j*π) := by
    simpa only [sub_add_cancel] using sin_add_nat_mul_pi (v-j*π) j
  rwa [e, ← mul_assoc, ← sq, parity_square, one_mul]

#print axioms signed_cos_grid
#print axioms signed_sin_grid_cell
end OpenMathResearch.LongCycleExcedances
