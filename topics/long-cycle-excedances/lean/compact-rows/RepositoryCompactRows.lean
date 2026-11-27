import CompactRowModel
import OriginalRoundedRows
import RepositoryQuotientShape
import LongCycleBounds.UniversalRecurrence

namespace RepositoryQuotientAudit
open Polynomial Finset LongCycles LongCycleFinite LongCycleBounds.Band
open OpenMathResearch.LongCycleExcedances TruncatedRows RunColors

/-- The row at the cutoff consists exactly of one cycle. -/
theorem compact_seed_eq {k : ℕ} (hk : 2 ≤ k) :
    canonicalReducedRow k k = eulerian (k-1) := by
  symm
  apply eq_canonical_of_factor
  change enumerator k k = X * eulerian (k-1)
  rw [enumerator_band hk le_rfl (by omega)]
  rw [Icc_eq_empty_of_lt (by omega : k/2 < k), sum_empty, add_zero]

def compactCycleWeight (k j : ℕ) : ℕ := ((descentCoeffs (k-1))[j]?.getD 0).toNat

theorem compact_seed_count (k : ℕ) (hk : 2 ≤ k) (j : ℕ) :
    compactCycleWeight k j = originalReducedCount k k j := by
  let z := (descentCoeffs (k-1))[j]?.getD 0
  have h : (z : ℝ) = (originalReducedCount k k j : ℝ) := by
    rw [originalReducedCount_eq, compact_seed_eq hk, ← ofCoeffs_descentCoeffs]
    exact (coeff_ofCoeffs _ _).symm
  have h' : z = (originalReducedCount k k j : ℤ) := by exact_mod_cast h
  change z.toNat = _
  rw [h', Int.toNat_natCast]

theorem compact_all_original (b k : ℕ) (hb : 0 < b) (hk : 2 ≤ k) (n i : ℕ) :
    Within (1/2^(b-1)) n (lowerRows b k (by omega) (compactCycleWeight k) n i)
      (((enumerator n k).divX).coeff i) := by
  apply rounded_counts_within (w:=i+1) hb hk (eulerian (k-1)) (compactCycleWeight k)
    _ (lowerRows b k (by omega) (compactCycleWeight k)) _ _ _ _ n i (by omega)
  · intro j
    rw [compact_seed_count k hk j, originalReducedCount_eq, compact_seed_eq hk]
  · intro m hm j _
    exact lowerRows_short _ hm _ _ _
  · intro j _
    rw [lowerRows_seed, compact_seed_count k hk j]
  · intro m _
    exact LongCycleBounds.Insertion.enumerator_succ hk
  · intro m hm j _
    exact lowerRows_succ _ hm _ _ _

/-- Uniform error in the alternating prefix from checked rounded coefficients,
on the entire size range used in the finite witness ledger. -/
theorem compact_original_prefix_error (k n w : ℕ) (hk : 2 ≤ k) (hn : n ≤ 1001) (y : ℝ) (hy : 0 ≤ y) :
    let low := lowerRows 48 k (by omega) (compactCycleWeight k) n
    |(∑ j ∈ range w, ((enumerator n k).divX).coeff j * (-y)^j) -
      ∑ j ∈ range w, (low j : ℝ) * (-y)^j| ≤
      (1 / (2:ℝ)^36) * ∑ j ∈ range w, (low j : ℝ)*y^j := by
  dsimp only
  have hn' : (n:ℝ) ≤ 1001 := by exact_mod_cast hn
  have hs : (n:ℝ) * (1/2^(48-1 : ℕ)) ≤ 1/2 := by norm_num; linarith
  apply (signed_prefix_error (by positivity) hs y hy _ _
    (fun j _ => compact_all_original 48 k (by decide) hk n j)).trans
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hy _))
  exact uniform_error_factor (b:=48) (by decide) (by omega)

#print axioms compact_seed_count
#print axioms compact_all_original
#print axioms compact_original_prefix_error
end RepositoryQuotientAudit
