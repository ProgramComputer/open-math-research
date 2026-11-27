import NormalizedColorBounds

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset

theorem real_count_below_cutoff {m k : ℕ} (hk : 2 ≤ k) (hm : 0 < m)
    (hmk : m < k) (i : ℕ) : ColorAnchor.realCount m i k = 0 := by
  rw [ColorAnchor.realCount_recurrence m i k hk hm]
  have he : Icc k m = ∅ := Finset.Icc_eq_empty_of_lt hmk
  rw [he, sum_empty]

theorem front_lag_zero_of_residual_count {n k p : ℕ} {V : ℝ}
    (hk : 2 ≤ k) (hkn : k ≤ n) (hcut : n+1 < 2*k) (hV : 0 ≤ V)
    (h : V ≤ (n.choose (k-1):ℝ)*
      ∑ j ∈ range (p+1), (j:ℝ)^(k-1)*ColorAnchor.realCount (n+1-k) (p-j) k) :
    V = 0 := by
  have hzero (i : ℕ) := real_count_below_cutoff hk
      (by omega : 0 < n+1-k) (by omega : n+1-k < k) i
  apply le_antisymm _ hV
  simpa only [hzero, mul_zero, sum_const_zero] using h

#print axioms real_count_below_cutoff
#print axioms front_lag_zero_of_residual_count
end OpenMathResearch.LongCycleExcedances
