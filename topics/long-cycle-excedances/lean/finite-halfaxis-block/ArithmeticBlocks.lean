import ShortInsertion
import SplitHalfAxis

namespace RepositoryQuotientAudit

/-- Check a bounded contiguous portion of a numerical predicate with one
kernel decision, and use the resulting theorem in a larger proof. -/
def arithmeticBlockOK (f : ℕ → Bool) (start size : ℕ) : Bool :=
  (List.range size).all fun j => f (start + j)

theorem arithmeticBlock_read {f : ℕ → Bool} {start size j : ℕ}
    (h : arithmeticBlockOK f start size = true)
    (hstart : start ≤ j) (hstop : j < start + size) : f j = true := by
  have hj : j - start ∈ List.range size := List.mem_range.mpr (by omega)
  have hsum : start + (j - start) = j := by omega
  simpa only [hsum] using List.all_eq_true.mp h (j - start) hj

end RepositoryQuotientAudit

#print axioms RepositoryQuotientAudit.arithmeticBlock_read
