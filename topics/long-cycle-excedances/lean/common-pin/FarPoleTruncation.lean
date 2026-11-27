import OpenMathResearch.DiskUniqueness
import Mathlib.Algebra.BigOperators.Intervals

namespace OpenMathResearch.LongCycleExcedances
open Finset

/-- Geometric bound for evaluating a coefficient truncation at a pole outside
the radius of the coefficient estimate. The exponents keep a square of the
pole modulus in the denominator, so a lattice sum is possible. -/
theorem norm_far_pole_truncation_le (T : ℕ → ℂ) (n : ℕ) {A R : ℝ} {w : ℂ}
    (hA : 0 ≤ A) (hR : 0 < R) (hw : R < ‖w‖)
    (hT : ∀ j < n, ‖T j‖ ≤ A / R^j) :
    ‖∑ j ∈ range n, T j * (1 / w^(n-j+1))‖ ≤
      (A / (R^(n-1)*‖w‖^2)) / (1-R/‖w‖) := by
  let W := ‖w‖
  have hW : 0 < W := hR.trans hw
  have hratio : R/W < 1 := (div_lt_one hW).2 hw
  have hpos : 0 ≤ A / (R^(n-1)*W^2) := by positivity
  have hgeom : (∑ j ∈ range n, (R/W)^j) ≤ 1/(1-R/W) := by
    exact OpenMathResearch.DiskUniqueness.geometric_tail_bound
      (fun j : ℕ => (R/W)^j) 1 (R/W) (by positivity) hratio (by simp) zero_le_one
      (fun j => by dsimp only; rw [pow_succ, mul_comm]) n
  calc
    _ ≤ ∑ j ∈ range n, ‖T j * (1 / w^(n-j+1))‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ range n, (A / (R^(n-1)*W^2)) * (R/W)^(n-1-j) := by
      apply sum_le_sum
      intro j hj
      have hlt := mem_range.mp hj
      simp only [norm_mul, norm_div, norm_one, norm_pow]
      change ‖T j‖ * (1 / W^(n-j+1)) ≤ _
      calc
        _ ≤ (A / R^j) * (1 / W^(n-j+1)) :=
          mul_le_mul_of_nonneg_right (hT j hlt) (by positivity)
        _ = _ := by
          have h1 : n-1 = j + (n-1-j) := by omega
          have h2 : n-j+1 = (n-1-j)+2 := by omega
          rw [h2, pow_add W, div_pow]
          conv_rhs => rw [← mul_div_assoc]
          have he : R^(n-1) = R^j * R^(n-1-j) := by
            rw [← pow_add, ← h1]
          rw [he]
          field_simp [hR.ne', hW.ne']
          ring
    _ = (A / (R^(n-1)*W^2)) * (∑ j ∈ range n, (R/W)^j) := by
      rw [← mul_sum, sum_range_reflect]
    _ ≤ (A / (R^(n-1)*W^2)) * (1/(1-R/W)) := mul_le_mul_of_nonneg_left hgeom hpos
    _ = _ := mul_one_div _ _

#print axioms norm_far_pole_truncation_le
end OpenMathResearch.LongCycleExcedances
