import GridSigns
import Mathlib.Topology.Order.IntermediateValue

namespace OpenMathResearch.LongCycleExcedances
open Set Real

private theorem exists_zero_of_signed_grid_endpoints {a b : ℝ} (hab : a ≤ b)
    (P : ℝ → ℝ) (hP : ContinuousOn P (Icc a b)) (j : ℕ)
    (ha : 0 < (-1:ℝ)^j * P a) (hb : 0 < (-1:ℝ)^(j+1) * P b) :
    ∃ x ∈ Ioo a b, P x = 0 := by
  have h₁ : P a ≠ 0 := by intro h; simp [h] at ha
  have h₂ : P b ≠ 0 := by intro h; simp [h] at hb
  have hzero : (0:ℝ) ∈ P '' Icc a b := by
    rw [pow_succ] at hb
    rcases Nat.even_or_odd j with h | h
    · rw [h.neg_one_pow] at ha hb
      exact intermediate_value_Icc' hab hP ⟨by linarith, by linarith⟩
    · rw [h.neg_one_pow] at ha hb
      exact intermediate_value_Icc hab hP ⟨by linarith, by linarith⟩
  obtain ⟨x,hx,hpx⟩ := hzero
  refine ⟨x,⟨lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_⟩,hpx⟩
  · intro he
    exact h₁ (he.symm ▸ hpx)
  · intro he
    exact h₂ (he ▸ hpx)

/-- The normalized cosine approximation and the pointwise next-row sign
supply a named open cell root and a signed upper value at every old zero. -/
theorem signed_grid_cell_of_row_estimates {a b : ℝ} (hab : a ≤ b) (n j : ℕ)
    {P Q normal phase : ℝ → ℝ}
    (ha : (n:ℝ)*a = (j:ℝ)*π) (hb : (n:ℝ)*b = ((j+1:ℕ):ℝ)*π)
    (hP : ContinuousOn P (Icc a b))
    (hphase : ∀ θ ∈ Icc a b, |phase θ-(n:ℝ)*θ| ≤ 1/2)
    (hpos : ∀ θ ∈ Icc a b, 0 < normal θ)
    (herror : ∀ θ ∈ Icc a b, |normal θ * P θ - cos (phase θ)| ≤ 1/6)
    (hnext : ∀ θ ∈ Icc a b, P θ = 0 → 0 < Q θ * (-sin (phase θ))) :
    (∃ θ ∈ Ioo a b, P θ = 0) ∧
    (∀ θ ∈ Icc a b, P θ = 0 → 0 < (-1:ℝ)^(j+1) * Q θ) := by
  have sample (x : ℝ) (hx : x ∈ Icc a b) (i : ℕ) (he : (n:ℝ)*x = (i:ℝ)*π) :
      0 < (-1:ℝ)^i * P x := by
    have h := hphase x hx
    rw [he] at h
    have hc := signed_cos_grid i h
    have herr := herror x hx
    have hnorm : |(-1:ℝ)^i| = 1 := by simp [abs_pow]
    rw [← one_mul |normal x*P x-cos (phase x)|, ← hnorm, ← abs_mul, mul_sub] at herr
    have hs : 0 < normal x * ((-1:ℝ)^i * P x) := by
      rw [show normal x*((-1:ℝ)^i*P x) = (-1:ℝ)^i*(normal x*P x) by ring]
      linarith [(abs_le.mp herr).1]
    exact pos_of_mul_pos_right hs (hpos x hx).le
  refine ⟨exists_zero_of_signed_grid_endpoints hab P hP j
    (sample a (left_mem_Icc.mpr hab) j ha) (sample b (right_mem_Icc.mpr hab) (j+1) hb), ?_⟩
  intro x hx hz
  have he := herror x hx
  rw [hz,mul_zero,zero_sub,abs_neg] at he
  have hlo : (j:ℝ)*π ≤ (n:ℝ)*x := by
    rw [← ha]
    exact mul_le_mul_of_nonneg_left hx.1 (by positivity)
  have hhi : ((n:ℝ)*x) ≤ ((j+1:ℕ):ℝ)*π := by
    rw [← hb]
    exact mul_le_mul_of_nonneg_left hx.2 (by positivity)
  have hsin := signed_sin_grid_cell j hlo hhi (hphase x hx) he
  have hp := mul_pos (hnext x hx hz) hsin
  have heq : (Q x * (-sin (phase x))) * ((-1:ℝ)^j * sin (phase x)) =
      ((-1:ℝ)^(j+1)*Q x) * (sin (phase x))^2 := by rw [pow_succ]; ring
  rw [heq] at hp
  exact pos_of_mul_pos_left hp (sq_nonneg _)

#print axioms signed_grid_cell_of_row_estimates
end OpenMathResearch.LongCycleExcedances
