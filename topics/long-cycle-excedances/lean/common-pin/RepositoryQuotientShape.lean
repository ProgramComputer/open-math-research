import RepositoryQuotientAdapter

namespace RepositoryQuotientAudit
open LongCycleBounds.Band LongCycles Polynomial

/-- The supplying cycle quotient is the canonical coefficient shift of the
original permutation sum on every nonempty row. -/
theorem generalCycleQuotient_eq_divX (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) :
    generalCycleQuotient n k = (enumerator n k).divX := by
  ext j
  rw [coeff_divX, actual_general_cycle_row hk hn, coeff_X_mul]

/-- Shape inputs for the root-list certificate on canonical original rows. -/
theorem original_divX_shape {n k : ℕ} (hk : 2 ≤ k) (hn : k ≤ n) :
    ((enumerator n k).divX).natDegree = n - 2 ∧
      ((enumerator n k).divX).Monic ∧ ((enumerator n k).divX).eval 0 = 1 := by
  simpa only [generalCycleQuotient_eq_divX n k (by omega) hk] using
    generalCycleQuotient_shape hk hn

/-- The portable readout specification for the canonical row. -/
theorem exact_coeff_eq_divX (n k j : ℕ) (hn : 0 < n) (hk : 2 ≤ k) :
    (cycleQuotientCoeff exactEulerianCoeff n k j : ℝ) = ((enumerator n k).divX).coeff j := by
  rw [← generalCycleQuotient_eq_divX n k hn hk, exact_coeff_eq_quotient]

end RepositoryQuotientAudit

#print axioms RepositoryQuotientAudit.generalCycleQuotient_eq_divX
#print axioms RepositoryQuotientAudit.original_divX_shape
#print axioms RepositoryQuotientAudit.exact_coeff_eq_divX
