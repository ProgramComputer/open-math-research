import CatalanStrictPeaksAllRoots
import CatalanStrictPeaksFarthestSign
import CatalanStrictPeaksMiddleRoots
import CatalanStrictPeaksRightmostRoot

/-!
# All-length strict Catalan interlacing

The analytic comparison uses the exact signs at the closest, middle and
farthest roots of the old row.
-/

namespace CatalanStrictPeaks

open OpenMathResearch.OrientedNegativeInterlace

private theorem interlacing_from_150 {n : ℕ} (hn : 150 ≤ n) : StrictlyInterlaces n := by
  obtain ⟨old, hOld, hMiddle⟩ := CutGeometry.middleRoot_signs_from_150 hn
  have hn' : 150 ≤ n + 1 := by omega
  obtain ⟨new, hNew⟩ := CutGeometry.roots_from_150 hn'
  apply next_from_old_root_signs hOld
  intro i
  by_cases hfirst : i.val = 0
  · rw [hfirst, zero_add, pow_one, neg_one_mul]
    exact neg_pos.mpr (RightEdge.rightmost_root_sign hn hOld hNew i hfirst)
  · by_cases hlast : i.val + 1 = rowDegree n
    · exact FarEdge.farthest_root_sign n hn old new hOld hNew i hlast
    · exact hMiddle i (Nat.pos_of_ne_zero hfirst) (by have hi := i.isLt; omega)

/-- Strict directed interlacing for the original Catalan word polynomials
at every successive pair of lengths. -/
theorem interlacing_all (n : ℕ) : StrictlyInterlaces n := by
  by_cases hn : n < 150
  · exact Finite.interlacing_before_150 n hn
  · exact interlacing_from_150 (by omega)

/-- Both assertions for strict peaks in Catalan words. The root
enumerations and the interlacing are ordered by increasing modulus. -/
theorem strict_peaks_all_lengths :
    (∀ n : ℕ, ∃ roots : Fin (rowDegree n) → ℝ, CompleteNegativeRoots (C n) roots) ∧
      ∀ n : ℕ, StrictlyInterlaces n :=
  ⟨roots_all, interlacing_all⟩

end CatalanStrictPeaks
