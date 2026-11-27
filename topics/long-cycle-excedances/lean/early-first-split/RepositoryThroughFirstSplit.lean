import FirstSplitFinite
import RepositoryEarlySector

namespace OpenMathResearch.LongCycleExcedances
open Polynomial LongCycles LongCycleFinite
noncomputable section

private theorem divX_of_original_factor {n k : ℕ} {P : ℝ[X]}
    (h : enumerator n k = X * P) : (enumerator n k).divX = P := by
  ext j
  simp only [coeff_divX, h, coeff_X_mul]

/-- Each cutoff at least eight has strict reduced and weak literal
interlacing at the first possible two-cycle row. -/
theorem original_first_split_all_cutoffs {k : ℕ} (hk : 8 ≤ k) :
    StrictNegativeInterlacing (enumerator (2*k-1) k).divX
      (enumerator (2*k) k).divX (2*k-3) ∧
    WeakRealInterlacing (enumerator (2*k-1) k) (enumerator (2*k) k) := by
  by_cases h : 55 ≤ k
  · exact original_at_first_split h
  have hs := finite_first_split_strict hk (by omega)
  obtain ⟨old,next⟩ := firstSplit_quotients k (by omega)
  refine ⟨?_, ?_⟩
  · rw [divX_of_original_factor old, divX_of_original_factor next]
    exact hs
  · rw [old,next]
    exact weak_mul_X_of_strict hs

/-- The lower size is below twice the cutoff. The upper size may equal it. -/
theorem original_through_first_split {n k : ℕ}
    (hk : 8 ≤ k) (lo : k ≤ n) (hi : n < 2*k) :
    StrictNegativeInterlacing (enumerator n k).divX
      (enumerator (n+1) k).divX (n-2) ∧
    WeakRealInterlacing (enumerator n k) (enumerator (n+1) k) := by
  by_cases h : n+1 < 2*k
  · exact original_before_first_split (by omega) lo h
  have lower : n = 2*k-1 := by omega
  have upper : 2*k-1+1 = 2*k := by omega
  have degree : 2*k-1-2 = 2*k-3 := by omega
  rw [lower, upper, degree]
  exact original_first_split_all_cutoffs hk

#print axioms original_first_split_all_cutoffs
#print axioms original_through_first_split
end
end OpenMathResearch.LongCycleExcedances
