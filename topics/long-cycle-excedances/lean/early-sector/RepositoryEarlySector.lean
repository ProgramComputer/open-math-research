import LongCycleBounds.InitialRows

namespace OpenMathResearch.LongCycleExcedances
open Polynomial LongCycles LongCycleFinite LongCycleBounds
noncomputable section

private theorem divX_of_original_factor {n k : ℕ} {P : ℝ[X]}
    (h : enumerator n k = X * P) : (enumerator n k).divX = P := by
  ext j
  simp only [coeff_divX, h, coeff_X_mul]

/-- Both actual rows have room for only one cycle. The index is the lower row size. -/
theorem original_before_first_split {n k : ℕ} (hk : 3 ≤ k)
    (lo : k ≤ n) (hi : n + 1 < 2 * k) :
    StrictNegativeInterlacing (enumerator n k).divX (enumerator (n+1) k).divX (n-2) ∧
      WeakRealInterlacing (enumerator n k) (enumerator (n+1) k) := by
  have old := beforeSplitRow (by omega : 2 ≤ k) lo (by omega : n < 2*k)
  have next := beforeSplitRow (by omega : 2 ≤ k) (by omega : k ≤ n+1) hi
  refine ⟨?_, beforeSplitInterlacing hk lo hi⟩
  rw [divX_of_original_factor old, divX_of_original_factor next]
  simpa only [show n-2+1=n-1 by omega, show n-1+1=n+1-1 by omega] using
    eulerian_consecutive_strict (n-2)

/-- Bowen Zuo's pinned strict first-split theorem stated in the canonical row quotients. -/
theorem original_at_first_split {k : ℕ} (hk : 55 ≤ k) :
    StrictNegativeInterlacing (enumerator (2*k-1) k).divX (enumerator (2*k) k).divX (2*k-3) ∧
      WeakRealInterlacing (enumerator (2*k-1) k) (enumerator (2*k) k) := by
  obtain ⟨old,next⟩ := firstSplit_quotients k (by omega)
  have hs := firstSplit55_strict k hk
  refine ⟨?_,?_⟩
  · rw [divX_of_original_factor old, divX_of_original_factor next]
    exact hs
  · rw [old,next]
    exact weak_mul_X_of_strict hs

#print axioms original_before_first_split
#print axioms original_at_first_split
end
end OpenMathResearch.LongCycleExcedances
