import HighHeightPointAdapter
import RepositoryLogTiltDiscrete

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open Finset Real OpenMathResearch.LongCycleExcedances

/-- The high-height contraction for the original cutoff logarithm that produces
the numerator of the actual permutation coefficient. -/
theorem original_high_height_numerator_contraction (k : ℕ) (hk : 100 ≤ k)
    (s : ℝ) (hhigh : 4*Real.sqrt (k:ℝ) < s) (w : ℂ) :
    let w₁ : ℂ := (s:ℂ)+(π:ℂ)*Complex.I
    let r := ‖w₁‖
    r ≤ ‖w‖ → ‖w‖ ≤ (1+1/(k:ℝ))*r →
    let w' := (((1-1/(k:ℝ))*r/‖w‖ : ℝ):ℂ)*w
    let w₁' := ((1-1/(k:ℝ):ℝ):ℂ)*w₁
    let g (j : ℕ) := (cutoffLogCoefficient k (-Real.exp (-s)) j : ℂ)
    ‖numeratorLog k g w-localLogRatio s w'‖ +
      ‖numeratorLog k g w₁-localLogRatio s w₁'‖ < 25 := by
  have hs0 : 0 ≤ 4*sqrt (k:ℝ) := by positivity
  have hs : 0 < s := hs0.trans_lt hhigh
  have hh := (sq_lt_sq₀ hs0 hs.le).mpr hhigh
  rw [mul_pow, sq_sqrt (by positivity : (0:ℝ) ≤ k)] at hh
  norm_num at hh
  apply high_height_numerator_at_points k hk s hs hh
  intro i hi
  have hik : i+1 < k := by have := mem_range.mp hi; omega
  simpa only [Nat.add_sub_cancel] using cutoffLogCoefficient_hasSum (by omega : 1 ≤ i+1) hik hs

#print axioms original_high_height_numerator_contraction
end RepositoryQuotientAudit
