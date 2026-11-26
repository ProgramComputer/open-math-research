import CatalanStrictPeaksIntervalData

/-!
# Kernel verification of the strict Catalan peak prefix

The data module contains candidate intervals. The kernel evaluates the
checked word recurrence and verifies every interval sign and separation.
-/

namespace CatalanStrictPeaks.Finite

open OpenMathResearch.OrientedNegativeInterlace

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rows_checked :
    (List.range 21).all (fun n => checkRow denominator n prefixBoxes[n]!) = true := by
  decide +kernel

private theorem pairs_checked :
    (List.range 20).all
      (fun n => checkPair n prefixBoxes[n]! prefixBoxes[n + 1]!) = true := by
  decide +kernel

private theorem row_checked (n : ℕ) (hn : n ≤ 20) :
    checkRow denominator n prefixBoxes[n]! = true :=
  List.all_eq_true.mp rows_checked n (List.mem_range.mpr (by omega))

/-- Rows 0 through 20 have only simple negative roots. -/
theorem roots_through_20 (n : ℕ) (hn : n ≤ 20) :
    ∃ r : Fin (rowDegree n) → ℝ, CompleteNegativeRoots (C n) r := by
  obtain ⟨r, hroots, _⟩ := checkRow_sound (b := denominator) (by decide) (row_checked n hn)
  exact ⟨r, hroots⟩

/-- The first 20 consecutive pairs strictly interlace in the specified orientation. -/
theorem interlacing_before_20 (n : ℕ) (hn : n < 20) : StrictlyInterlaces n := by
  have hp := List.all_eq_true.mp pairs_checked n (List.mem_range.mpr hn)
  exact checkPair_sound (b := denominator) (by decide) (row_checked n (by omega))
    (row_checked (n + 1) (by omega)) hp

end CatalanStrictPeaks.Finite
