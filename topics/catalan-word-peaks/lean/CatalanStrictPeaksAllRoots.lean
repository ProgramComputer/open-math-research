import CatalanStrictPeaksPhaseBridge
import CatalanStrictPeaksPrefix

/-!
# Simple negative zeros at every length

The exact finite prefix and the analytic checkpoint proof together
give a complete root list for each original strict-peak polynomial.
-/

namespace CatalanStrictPeaks

open OpenMathResearch.OrientedNegativeInterlace

/-- Every Catalan strict-peak row has only simple negative zeros. -/
theorem roots_all (n : ℕ) :
    ∃ roots : Fin (rowDegree n) → ℝ, CompleteNegativeRoots (C n) roots := by
  by_cases hn : n ≤ 150
  · exact CatalanStrictPeaks.Finite.roots_through_150 n hn
  · exact CutGeometry.roots_from_150 (Nat.le_of_lt (Nat.lt_of_not_ge hn))

end CatalanStrictPeaks
