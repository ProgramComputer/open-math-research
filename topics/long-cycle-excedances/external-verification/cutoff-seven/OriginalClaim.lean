import LongCycleBounds.SevenCutoffAllSizes

namespace IndependentCutoffSeven
open LongCycles LongCycleFinite Polynomial

/-- At cutoff seven the lower row is indexed by m, with first pair (7,8).
Both assertions use the unweighted strict-excedance enumerators. -/
theorem from_lower_size (m : ℕ) (hm : 7 ≤ m) :
    (∃ P Q : Polynomial ℝ,
      enumerator m 7 = X * P ∧ enumerator (m+1) 7 = X * Q ∧
      StrictNegativeInterlacing P Q (m-2)) ∧
      WeakRealInterlacing (enumerator m 7) (enumerator (m+1) 7) := by
  have h := LongCycleBounds.SevenCutoff.all_sizes (n:=m+1) (by omega : 8 ≤ m+1)
  simpa [LongCycleFinite.K7Prefix.OriginalPair] using h

end IndependentCutoffSeven
