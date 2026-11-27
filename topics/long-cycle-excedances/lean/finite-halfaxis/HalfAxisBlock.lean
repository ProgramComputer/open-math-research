import ExactInsertionTable
import HalfAxisDyadic

namespace RepositoryQuotientAudit

open LongCycles LongCycleFinite

/-- One exact coefficient table serves both rows of every checked old-size
pair. The final supported row is the successor of the last checked old size. -/
theorem original_weak_block_of_checked_half_axis {k first last width : ℕ}
    (hk : 2 ≤ k) (hfirst : k ≤ first) (hwidth : last - 2 < width)
    (row : ℕ → List ℕ)
    (hshort : ∀ n < k, ∀ i < width, exactListRead (row n) i = 0)
    (hseed : ∀ i < width, exactListRead (row k) i = compactCycleWeight k i)
    (hstep : ∀ n, k ≤ n → n < last → ∀ i < width,
      exactListRead (row (n + 1)) i =
        exactListStep k n (compactCycleWeight k) (row n) (row (n + 1 - k)) i)
    (hlen : ∀ n ≤ last, (row n).length ≤ width)
    (windows : (n : ℕ) → Fin ((n - 2) / 2) → HalfAxisDyadicWindow)
    (hcheck : ∀ n, first ≤ n → n < last →
      halfAxisDyadicOK n ((row n).map Int.ofNat) ((row (n+1)).map Int.ofNat)
        (windows n) = true) :
    ∀ n, first ≤ n → n < last →
      WeakRealInterlacing (enumerator n k) (enumerator (n + 1) k) := by
  intro n hn hlast
  have hk' : k ≤ n := hfirst.trans hn
  have hn' : n + 1 ≤ last := by omega
  have reads := exactListTable_reads hk row hshort hseed hstep
  refine original_weak_of_checked_half_axis hk hk' _ _ ?_ ?_ _ (hcheck n hn hlast)
  · exact ofCoeffs_eq_original_of_reads hk hk' (by omega) _ (hlen n (by omega))
      (reads n (by omega))
  · exact ofCoeffs_eq_original_of_reads hk (by omega) (by omega) _ (hlen (n+1) hn')
      (reads (n+1) hn')

end RepositoryQuotientAudit

#print axioms RepositoryQuotientAudit.original_weak_block_of_checked_half_axis
