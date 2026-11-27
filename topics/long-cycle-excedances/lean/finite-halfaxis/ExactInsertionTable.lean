import RepositoryCompactRows

namespace RepositoryQuotientAudit

open Polynomial Finset LongCycles LongCycleFinite
open OpenMathResearch.LongCycleExcedances TruncatedRows RunColors

def exactListRead (row : List ℕ) (j : ℕ) : ℕ := row[j]?.getD 0

private def gridSum (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => gridSum f n + f n

private theorem gridSum_eq (f : ℕ → ℕ) (n : ℕ) :
    gridSum f n = ∑ j ∈ range n, f j := by
  induction n with
  | zero => simp [gridSum]
  | succ n ih => rw [gridSum, sum_range_succ, ih]

/-- Executable exact insertion on a rectangular zero-padded table. -/
def exactListStep (k n : ℕ) (weight : ℕ → ℕ) (row lag : List ℕ) : ℕ → ℕ
  | 0 => exactListRead row 0
  | i + 1 => (i + 2) * exactListRead row (i + 1) + (n - (i + 1)) * exactListRead row i +
      Nat.fast_choose n (k - 1) * gridSum (fun j => weight j * exactListRead lag (i - j)) (i + 1)

theorem exactListStep_eq (k n : ℕ) (weight : ℕ → ℕ) (row lag : List ℕ) (i : ℕ) :
    exactListStep k n weight row lag i =
      positiveStep k n weight (exactListRead row) (exactListRead lag) i := by
  cases i <;> simp [exactListStep, positiveStep, gridSum_eq, Nat.fast_choose,
    ← Nat.choose_eq_descFactorial_div_factorial]

theorem exactListTable_reads {k limit width : ℕ} (hk : 2 ≤ k)
    (row : ℕ → List ℕ)
    (short : ∀ n < k, ∀ i < width, exactListRead (row n) i = 0)
    (seed : ∀ i < width, exactListRead (row k) i = compactCycleWeight k i)
    (step : ∀ n, k ≤ n → n < limit → ∀ i < width,
      exactListRead (row (n + 1)) i =
        exactListStep k n (compactCycleWeight k) (row n) (row (n + 1 - k)) i) :
    ∀ n ≤ limit, ∀ i < width, exactListRead (row n) i = originalReducedCount n k i := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn i hi
    rcases lt_trichotomy n k with h | heq | h
    · rw [short n h i hi, originalReducedCount_short n k i h]
    · subst n
      rw [seed i hi, compact_seed_count k hk]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      rw [step m (by omega) (by omega) i hi, exactListStep_eq,
          original_count_step m k hk (by omega) (eulerian (k-1)) (compactCycleWeight k)
            (fun j => by rw [compact_seed_count k hk, originalReducedCount_eq, compact_seed_eq hk])
            (LongCycleBounds.Insertion.enumerator_succ hk)]
      have hm (j : ℕ) (hj : j < width) :=
        ih m (by omega) (by omega) j hj
      have hr (j : ℕ) (hj : j < width) :=
        ih (m + 1 - k) (by omega) (by omega) j hj
      cases i with
      | zero => simpa only [positiveStep] using hm 0 hi
      | succ i =>
        simp only [positiveStep, hm (i+1) hi, hm i (by omega : i < width)]
        congr 2
        apply Finset.sum_congr rfl
        intro j hj
        rw [hr (i-j) (by omega)]

theorem ofCoeffs_eq_original_of_reads {n k width : ℕ} (hk : 2 ≤ k) (hn : k ≤ n)
    (hdeg : n - 2 < width) (row : List ℕ) (hlen : row.length ≤ width)
    (hread : ∀ i < width, exactListRead row i = originalReducedCount n k i) :
    ofCoeffs (row.map Int.ofNat) = (enumerator n k).divX := by
  ext i
  rw [coeff_ofCoeffs]
  by_cases hi : i < width
  · rw [List.getElem?_map, ← show ((exactListRead row i : ℕ) : ℝ) =
        (((row[i]?).map Int.ofNat).getD 0 : ℤ) from by
          unfold exactListRead
          cases row[i]? <;> simp,
      hread i hi, originalReducedCount_eq]
    rfl
  · have hnth : (row.map Int.ofNat)[i]? = none :=
      List.getElem?_eq_none (by simpa using (show row.length ≤ i by omega))
    rw [hnth]
    simp only [Option.getD_none, Int.cast_zero]
    symm
    exact coeff_eq_zero_of_natDegree_lt (by rw [(original_divX_shape hk hn).1]; omega)

end RepositoryQuotientAudit

#print axioms RepositoryQuotientAudit.exactListTable_reads
#print axioms RepositoryQuotientAudit.ofCoeffs_eq_original_of_reads
