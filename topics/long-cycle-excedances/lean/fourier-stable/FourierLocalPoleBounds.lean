import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Metric Set

/-- A disk of half the radius of a pole-free disk gives a single relative
denominator bound for every pole, even for poles arbitrarily far away. -/
theorem local_pole_ratio {ι : Type*} (P : ι → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hp : ∀ i, P i ∉ U) {z : ℂ} (hz : z ∈ U) :
    ∃ δ M : ℝ, 0 < δ ∧ 0 < M ∧ ball z δ ⊆ U ∧
      ∀ i w, w ∈ ball z δ → ‖P i‖ ≤ M*‖P i-w‖ := by
  obtain ⟨a,ha,hball⟩ := Metric.isOpen_iff.mp hU z hz
  let δ := a/2
  have hd : 0 < δ := half_pos ha
  let B := ‖z‖+δ
  have hB : 0 ≤ B := add_nonneg (norm_nonneg _) hd.le
  refine ⟨δ,1+B/δ,hd,by positivity, (ball_subset_ball (by dsimp [δ]; linarith)).trans hball, ?_⟩
  intro i w hw
  have hdist : a ≤ dist (P i) z := le_of_not_gt (fun h => hp i (hball (mem_ball.mpr h)))
  have hnear := mem_ball.mp hw
  have hsep : δ ≤ ‖P i-w‖ := by
    have ht := dist_triangle (P i) w z
    rw [dist_eq_norm (P i) w] at ht
    dsimp [δ] at hnear ⊢
    linarith
  have hnorm : ‖w‖ ≤ B := by
    have ht := norm_add_le (w-z) z
    rw [sub_add_cancel] at ht
    rw [dist_eq_norm] at hnear
    dsimp only [B]; linarith
  have hratio : B ≤ (B/δ)*‖P i-w‖ := by
    calc
      B = (B/δ)*δ := (div_mul_cancel₀ _ hd.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsep (div_nonneg hB hd.le)
  have ht := norm_add_le (P i-w) w
  rw [sub_add_cancel] at ht
  rw [add_mul,one_mul]
  linarith [hnorm.trans hratio]

#print axioms local_pole_ratio
end OpenMathResearch.LongCycleExcedances
