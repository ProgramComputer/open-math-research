import CompactPoint
import RepositoryCompactRows

namespace RepositoryQuotientAudit
open Polynomial Finset LongCycles
open OpenMathResearch.LongCycleExcedances TruncatedRows IntegerSign

/-- Kernel specification of the compact integer row presented to the endpoint checker. -/
def compactCoeff (words : List ℕ) (i : ℕ) : ℤ := decode 48 (words[i]?.getD 0)

/-- The data assumptions are integer comparisons and an identification of the
packed words with the computable positive rounded recurrence. No exact original
coefficient, polynomial evaluation, tail estimate or root assumption is needed. -/
theorem original_signed_of_packed_words (k n w : ℕ) (hk : 2 ≤ k) (hn : n ≤ 1001)
    (words : List ℕ) (p : ℤ) (D : ℕ) (s : ℤ)
    (rows : ∀ i, i<w → decode 48 (words[i]?.getD 0) =
      lowerRows 48 k (by omega) (compactCycleWeight k) n i)
    (check : packedPointCheck n w (compactCoeff words) p D s = true) :
    0 < (s:ℝ)*((enumerator n k).divX).eval (-(((p:ℚ)/D : ℚ):ℝ)) := by
  apply original_signed_of_packed_margin n k w hk (compactCoeff words) p D s check
  let y := (p:ℚ)/D
  have ok := check
  unfold packedPointCheck at ok
  obtain ⟨hd,hp,_⟩ := of_decide_eq_true ok
  have hy : (0:ℚ) ≤ y := div_nonneg (by exact_mod_cast hp) (Nat.cast_nonneg _)
  have h := compact_original_prefix_error k n w hk hn (y:ℝ) (by exact_mod_cast hy)
  let low := lowerRows 48 k (by omega) (compactCycleWeight k) n
  have decode_sum (t : ℝ) :
      ∑ i ∈ range w, (compactCoeff words i : ℝ)*t^i = ∑ i ∈ range w, (low i : ℝ)*t^i := by
    apply sum_congr rfl
    intro i hi
    simp only [compactCoeff,Int.cast_natCast,rows i (mem_range.mp hi),low]
  dsimp only
  rw [decode_sum, decode_sum]
  exact h

#print axioms original_signed_of_packed_words
end RepositoryQuotientAudit
