import OpenMathResearch.FirstLevelHits
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace BalancedEventual

open Set Filter OpenMathResearch.FirstLevelHits
open scoped Topology

/-- In the balanced-array phase argument the internal levels are the multiples
`k * Real.pi` with `1 ≤ k < D`. The upper endpoint may equal `D * Real.pi`. -/
theorem exists_ordered_integer_phase_radii {phase : ℝ → ℝ} {l u : ℝ} {D : ℕ}
    (hf : Continuous (fun x => phase (Real.exp x)))
    (hl : Tendsto (fun x => phase (Real.exp x)) atBot (𝓝 l))
    (hu : Tendsto (fun x => phase (Real.exp x)) atTop (𝓝 u))
    (hleft : l < Real.pi) (hright : (D : ℝ) * Real.pi ≤ u) :
    ∃ radius : {k : ℕ // 1 ≤ k ∧ k < D} → ℝ,
      StrictMono radius ∧ (∀ k, 0 < radius k) ∧
        ∀ k, IsLeast {v | 0 < v ∧ phase v = (k.val : ℝ) * Real.pi} (radius k) := by
  obtain ⟨hit, hmono, hpos, hhit⟩ := exists_ordered_positive_phase_radii hf hl hu
  let level (k : {k : ℕ // 1 ≤ k ∧ k < D}) : Ioo l u :=
    ⟨(k.val : ℝ) * Real.pi, by
      have hlo : (1 : ℝ) ≤ (k.val : ℝ) := by exact_mod_cast k.property.1
      have hhi : (k.val : ℝ) < (D : ℝ) := by exact_mod_cast k.property.2
      exact ⟨hleft.trans_le (by simpa using mul_le_mul_of_nonneg_right hlo Real.pi_pos.le),
        (mul_lt_mul_of_pos_right hhi Real.pi_pos).trans_le hright⟩⟩
  have hlevel : StrictMono level := by
    intro i j hij
    have hij' : i.val < j.val := hij
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hij') Real.pi_pos
  exact ⟨hit ∘ level, hmono.comp hlevel, fun k => hpos (level k), fun k => hhit (level k)⟩

/-- The endpoint limits and the support degree used in the dimension-uniform
balanced-array proof imply the internal first-hit radius family. -/
theorem exists_balanced_phase_radii (n d r : ℕ) (hd : 2 ≤ d) {phase : ℝ → ℝ}
    (hf : Continuous (fun x => phase (Real.exp x)))
    (hl : Tendsto (fun x => phase (Real.exp x)) atBot
      (𝓝 (-(((d : ℝ) - 1) / 2) * (Real.pi / d))))
    (hu : Tendsto (fun x => phase (Real.exp x)) atTop
      (𝓝 (((n : ℝ) * r / d) * Real.pi))) :
    ∃ radius : {k : ℕ // 1 ≤ k ∧ k < n * r / d} → ℝ,
      StrictMono radius ∧ (∀ k, 0 < radius k) ∧
        ∀ k, IsLeast {v | 0 < v ∧ phase v = (k.val : ℝ) * Real.pi} (radius k) := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide) hd : 0 < d)
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (le_trans (by decide) hd : 1 ≤ d)
  have hfloor : ((n * r / d : ℕ) : ℝ) ≤ (n : ℝ) * r / d := by
    apply (le_div_iff₀ hd').2
    exact_mod_cast Nat.div_mul_le_self (n * r) d
  apply exists_ordered_integer_phase_radii hf hl hu
  · exact lt_of_le_of_lt
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg (sub_nonneg.mpr hd1)
        (by positivity))) (div_nonneg Real.pi_pos.le hd'.le))
      Real.pi_pos
  · exact mul_le_mul_of_nonneg_right hfloor Real.pi_pos.le

#print axioms exists_ordered_integer_phase_radii
#print axioms exists_balanced_phase_radii

end BalancedEventual
