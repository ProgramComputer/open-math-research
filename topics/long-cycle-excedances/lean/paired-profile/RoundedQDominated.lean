import RoundedProductTable

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances
open Finset

/-- Any verified upper recurrence dominates the outward-rounded coefficient
sequence through the checked cap. -/
theorem roundedQ_le_recurrence {G N : ℕ} (hG : 0 < G) (l q : ℕ → ℕ)
    (hq : q 0 = G)
    (hrec : ∀ m < N, ∑ ij ∈ antidiagonal m, (ij.1+1)*l (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*G)
    (b : ℕ) (hb : b ≤ N) : roundedQ G l b ≤ q b := by
  induction b using Nat.strong_induction_on with
  | h b ih =>
    cases b with
    | zero => rw [roundedQ_zero, hq]
    | succ m =>
      have hsum :
          (∑ ij ∈ antidiagonal m, (ij.1+1)*l (ij.1+1)*roundedQ G l ij.2) ≤
          ∑ ij ∈ antidiagonal m, (ij.1+1)*l (ij.1+1)*q ij.2 := by
        apply sum_le_sum
        intro ij hij
        have he := mem_antidiagonal.mp hij
        exact Nat.mul_le_mul_left _ (ih ij.2 (by omega) (by omega))
      have hnum := hsum.trans (hrec m (by omega))
      let D := (m+1)*G
      have hD : 0 < D := Nat.mul_pos (by omega) hG
      rw [roundedQ_step]
      apply Nat.lt_succ_iff.mp
      apply (Nat.div_lt_iff_lt_mul hD).mpr
      have hn : (∑ ij ∈ antidiagonal m, (ij.1+1)*l (ij.1+1)*roundedQ G l ij.2) ≤
          q (m+1)*D := by
        dsimp [D]
        exact hnum.trans_eq (by ac_rfl)
      rw [show (q (m+1)).succ*D = q (m+1)*D+D from Nat.succ_mul _ _]
      change _ + D - 1 < q (m+1)*D + D
      omega

#print axioms roundedQ_le_recurrence
end OpenMathResearch.LongCycleExcedances
