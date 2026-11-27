import ColorTransformError
import LongCycleRunColors
import LongCycleBounds.AnchoredRows
import LongCycleBounds.DescentRows
import LongCycleBounds.GeneralCycleSupports

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open LongCycles PowerSeries Finset OpenMathResearch.LongCycleExcedances

theorem original_color_transform_anchor {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k) :
    colorTransform n (enumerator n k) = ∑ a ∈ Icc k n,
      C (R := ℝ) (((n-1).choose (a-1)):ℝ)*colorPowerSeries (a-1)*
        colorTransform (n-a) (enumerator (n-a) k) :=
  colorTransform_anchor eulerian LongCycleBounds.longEulerian_one LongCycleBounds.longEulerian_succ
    (fun m => enumerator m k) hk (LongCycleBounds.Anchored.anchored_row_recurrence hk (⟨0,hn⟩ : Fin n))

/-- The color-cycle recurrence with the zero-size convention determines
the entire series from the literal permutation polynomials. -/
theorem original_color_series_unique {k : ℕ} (hk : 2 ≤ k) (F : ℕ → PowerSeries ℝ)
    (hzero : F 0=1) (hrec : ∀ n, 0<n → F n = ∑ a ∈ Icc k n,
      C (R := ℝ) (((n-1).choose (a-1)):ℝ)*colorPowerSeries (a-1)*F (n-a)) (n : ℕ) :
    F n=colorTransform n (enumerator n k) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with h|h
    · subst n
      have hempty : enumerator 0 k=1 := by
        rw [LongCycleBounds.CycleCount.enumerator_ordered_cycle_rows hk]
        simp [LongCycleBounds.CycleCount.orderedCycleRow]
      rw [hzero,hempty,colorTransform_zero]
    · rw [hrec n h, original_color_transform_anchor h hk]
      apply sum_congr rfl
      intro a ha
      rw [ih (n-a) (by have := (mem_Icc.mp ha).1; omega)]

/-- The normalized finite anchored counts coincide with the explicit
binomial transform once their combinatorial recurrence is supplied. -/
theorem original_color_count_of_recurrence {k : ℕ} (hk : 2 ≤ k) (D : ℕ → ℕ → ℝ)
    (hzero : ∀ p, D 0 p=if p=0 then 1 else 0)
    (hrec : ∀ n p, 0<n → D n p = ∑ a ∈ Icc k n, (((n-1).choose (a-1)):ℝ)*
      ∑ j ∈ range (p+1), (j:ℝ)^(a-1)*D (n-a) (p-j)) {n : ℕ} (hn : 0<n) (p : ℕ) :
    D n p=∑ s ∈ range (p+1), (enumerator n k).coeff s*
        (((n-1+(p-s)).choose (n-1)):ℝ) := by
  let F (n : ℕ) : PowerSeries ℝ := mk (D n)
  have hz : F 0=1 := by
    ext q
    simp only [F,coeff_mk,coeff_one,hzero]
  have hr (m : ℕ) (hm : 0<m) : F m=∑ a ∈ Icc k m,
      C (R := ℝ) (((m-1).choose (a-1)):ℝ)*colorPowerSeries (a-1)*F (m-a) := by
    ext q
    simp only [F,coeff_mk,map_sum,color_convolution_coeff]
    exact hrec m q hm
  have he := congrArg (coeff (R := ℝ) p) (original_color_series_unique hk F hz hr n)
  simpa only [F,coeff_mk,colorTransform_coeff _ hn] using he

#print axioms original_color_count_of_recurrence

/-- An integer-power error bound if the transformed count is bounded by all
color assignments after dividing out the color-permutation factor. -/
theorem original_color_transform_error {n p k : ℕ} (hn : 0<n) (hp : 0<p) (hk : 2≤k)
    (hcount : coeff (R := ℝ) p (colorTransform n (enumerator n k)) ≤ (p:ℝ)^n) :
    0 ≤ (coeff (R := ℝ) p (colorTransform n (enumerator n k))-(enumerator n k).coeff p)/(p:ℝ)^n ∧
    (coeff (R := ℝ) p (colorTransform n (enumerator n k))-(enumerator n k).coeff p)/(p:ℝ)^n ≤
      2*((n:ℝ)*(1-1/(p:ℝ))^n) := by
  have hb (s : ℕ) : 0 ≤ (enumerator n k).coeff s ∧ (enumerator n k).coeff s ≤ (s:ℝ)^n :=
    RunColors.original_coeff_envelope n k s hk
  exact ⟨(color_transform_error _ hn hp hb).1,color_transform_error_twice _ hn hp hb hcount⟩

#print axioms original_color_transform_anchor
#print axioms original_color_series_unique
#print axioms original_color_transform_error
end RepositoryQuotientAudit
