import NormalizedColorBounds
import RepositoryColorTransform

set_option autoImplicit false
namespace RepositoryQuotientAudit
open LongCycles PowerSeries OpenMathResearch.LongCycleExcedances

/-- The normalized count of actual words and color permutations equals the
binomial transform of the original permutation enumerator. -/
theorem original_color_count_eq_transform {n p k : ℕ} (hn : 0 < n) (hk : 2 ≤ k) :
    ColorAnchor.realCount n p k = coeff ℝ p (colorTransform n (enumerator n k)) := by
  rw [original_color_count_of_recurrence hk (fun n p => ColorAnchor.realCount n p k)
    (fun p => ColorAnchor.realCount_zero p k (by omega))
    (fun n p hn => ColorAnchor.realCount_recurrence n p k hk hn) hn p,
    colorTransform_coeff _ hn]

/-- The actual normalized orbit-acceptance density differs from the original
scaled coefficient by the stated explicit error, without a count hypothesis. -/
theorem original_color_acceptance_error {n p k : ℕ} (hn : 0 < n) (hp : 0 < p) (hk : 2 ≤ k) :
    0 ≤ (ColorAnchor.realCount n p k - (enumerator n k).coeff p) / (p:ℝ)^n ∧
      (ColorAnchor.realCount n p k - (enumerator n k).coeff p) / (p:ℝ)^n ≤
        2 * ((n:ℝ) * (1 - 1 / (p:ℝ))^n) := by
  have h := original_color_count_eq_transform (p := p) hn hk
  have hu : coeff ℝ p (colorTransform n (enumerator n k)) ≤ (p:ℝ)^n :=
    h ▸ (ColorAnchor.realCount_bounds n p k).2
  rw [h]
  exact original_color_transform_error hn hp hk hu

#print axioms original_color_count_eq_transform
#print axioms original_color_acceptance_error
end RepositoryQuotientAudit
