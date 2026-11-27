import FourierPolePair

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Filter Real
open scoped Topology

theorem normalizedPole_nonneg (p : ℂ) (R x : ℝ) : 0 ≤ normalizedPole p R x :=
  div_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)

/-- Uniform in the angle even when the pole is inside the circle. -/
theorem normalizedPole_le_gap {p : ℂ} {R : ℝ} (hR : 0 < R) (hp : ‖p‖ ≠ R) (x : ℝ) :
    normalizedPole p R x ≤ √(poleGap p R) / |‖p‖-R| := by
  have h := abs_norm_sub_norm_le p (circleMap 0 R x)
  rw [norm_circleMap_zero,abs_of_pos hR] at h
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (abs_pos.mpr (sub_ne_zero.mpr hp)) h

theorem normalizedPole_le_two {p : ℂ} {R : ℝ} (hR : 0 < R) (hp : 2*R ≤ ‖p‖) (x : ℝ) :
    normalizedPole p R x ≤ 2 := by
  have hg : R < ‖p‖ := by linarith
  apply (normalizedPole_le_gap hR hg.ne' x).trans
  rw [abs_of_pos (sub_pos.mpr hg),div_le_iff₀ (sub_pos.mpr hg)]
  have hl : √(poleGap p R) ≤ ‖p‖ := by
    apply (Real.sqrt_le_iff).2
    refine ⟨norm_nonneg _, ?_⟩
    rw [poleGap,abs_of_pos (sub_pos.mpr (sq_lt_sq' (by linarith [norm_nonneg p]) hg))]
    nlinarith [sq_nonneg R]
  linarith

/-- For finitely many exceptional radii, the bound is the sum of their individual
bounds plus two. The remaining poles use the same constant. -/
theorem normalizedPole_uniform (P : ℕ → ℂ) {R : ℝ} (hR : 0 < R) (hp : ∀ i, ‖P i‖ ≠ R)
    (hfar : ∀ᶠ i in atTop, 2*R ≤ ‖P i‖) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i x, normalizedPole (P i) R x ≤ M := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 hfar
  let c := fun i => √(poleGap (P i) R)/|‖P i‖-R|
  have hc (i) : 0 ≤ c i := div_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hs : 0 ≤ ∑ i ∈ Finset.range N, c i := Finset.sum_nonneg (fun i _ => hc i)
  refine ⟨2+∑ i ∈ Finset.range N, c i, by linarith, ?_⟩
  intro i x
  by_cases hi : i < N
  · have hb := Finset.single_le_sum (f := c) (fun j _ => hc j) (Finset.mem_range.mpr hi)
    exact (normalizedPole_le_gap hR (hp i) x).trans (by dsimp only [c] at hb; linarith)
  · exact (normalizedPole_le_two hR (hN i (le_of_not_gt hi)) x).trans (by linarith)

#print axioms normalizedPole_le_two
#print axioms normalizedPole_uniform
end OpenMathResearch.LongCycleExcedances
