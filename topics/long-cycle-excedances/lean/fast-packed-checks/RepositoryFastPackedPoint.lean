import FastPackedPoint
import RepositoryPackedPoint

namespace RepositoryQuotientAudit
open Polynomial LongCycles
open OpenMathResearch.LongCycleExcedances IntegerSign TruncatedRows

theorem original_signed_of_fast_packed_words (k n level bits : ℕ) (hk : 2 ≤ k) (hn : n ≤ 1001)
    (words : List ℕ) (p s : ℤ)
    (rows : ∀ i, i < words.length → decode 48 (words[i]?.getD 0) =
      lowerRows 48 k (by omega) (compactCycleWeight k) n i)
    (check : fastCoarseCheck n level bits words p s = true) :
    0 < (s:ℝ)*((enumerator n k).divX).eval (-(((p:ℚ)/(2^bits:ℕ) : ℚ):ℝ)) := by
  rw [fastCoarseCheck_eq] at check
  exact original_signed_of_packed_words k n words.length hk hn words p (2^bits) s rows
    (packed_check_of_coarse n words.length level (compactCoeff words) p (2^bits) s check)

#print axioms original_signed_of_fast_packed_words
end RepositoryQuotientAudit
