import ExactInsertionTable

namespace RepositoryQuotientAudit

open Finset
open OpenMathResearch.LongCycleExcedances.TruncatedRows

private theorem sum_range_list (f : ℕ → ℕ) (n : ℕ) :
    (List.range n).foldl (fun a j => a + f j) 0 = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← ih]
    rfl

/-- Restrict the correction sum to the support of the cutoff cycle. -/
def shortExactStep (k n : ℕ) (weight : ℕ → ℕ) (row lag : List ℕ) : ℕ → ℕ
  | 0 => exactListRead row 0
  | i + 1 => (i + 2) * exactListRead row (i + 1) + (n - (i + 1)) * exactListRead row i +
      Nat.fast_choose n (k - 1) * (List.range (min (i + 1) (k - 1))).foldl
        (fun acc j => acc + weight j * exactListRead lag (i - j)) 0

theorem shortExactStep_eq (k n : ℕ) (weight : ℕ → ℕ)
    (hwhite : ∀ j, k - 1 ≤ j → weight j = 0) (row lag : List ℕ) (i : ℕ) :
    shortExactStep k n weight row lag i = exactListStep k n weight row lag i := by
  rw [exactListStep_eq]
  cases i with
  | zero => rfl
  | succ i =>
    have hs := Finset.sum_subset (f := fun j => weight j * exactListRead lag (i - j))
      (Finset.range_mono (Nat.min_le_left (i+1) (k-1)))
      (by
        intro j hj hnot
        have hj' := Finset.mem_range.mp hj
        have hnot' : ¬ j < min (i+1) (k-1) := fun h => hnot (Finset.mem_range.mpr h)
        change weight j * exactListRead lag (i - j) = 0
        rw [hwhite j (by omega), zero_mul])
    simp only [shortExactStep, positiveStep, sum_range_list, hs, Nat.fast_choose,
      ← Nat.choose_eq_descFactorial_div_factorial]

theorem compactCycleWeight_support (k j : ℕ) (hk : 2 ≤ k) (hj : k - 1 ≤ j) :
    compactCycleWeight k j = 0 := by
  have hdegree := (original_divX_shape hk (le_refl k)).1
  have hz : ((LongCycles.enumerator k k).divX).coeff j = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdegree]; omega)
  rw [compact_seed_count k hk]
  have hc := OpenMathResearch.LongCycleExcedances.originalReducedCount_eq k k j
  change (↑(OpenMathResearch.LongCycleExcedances.originalReducedCount k k j) : ℝ) =
    ((LongCycles.enumerator k k).divX).coeff j at hc
  exact_mod_cast hc.trans hz

end RepositoryQuotientAudit

#print axioms RepositoryQuotientAudit.shortExactStep_eq
#print axioms RepositoryQuotientAudit.compactCycleWeight_support
