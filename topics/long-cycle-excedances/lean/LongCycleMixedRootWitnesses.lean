import OpenMathResearch.OrientedNegativeInterlace

/-!
# Interlacing from mixed old-root witnesses

A closed window in increasing modulus order either consists of a known old
root or has opposite old endpoint signs. Alternating next-row signs at both
endpoints force a next root in each complementary gap.
-/

namespace OpenMathResearch.LongCycleExcedances

open Polynomial OrientedNegativeInterlace

/-- Ordered old-root point witnesses and sign-changing brackets give complete
negative root lists in consecutive degrees. The next roots lie strictly in
the complementary gaps, including the two outer gaps. -/
theorem interlace_of_mixed_root_witnesses {m : ℕ} {P Q : ℝ[X]}
    (l u : Fin m → ℝ) (hP : P ≠ 0) (hdegP : P.natDegree = m)
    (hdegQ : Q.natDegree = m + 1) (hzero : 0 < Q.eval 0)
    (hlead : 0 < Q.leadingCoeff) (hpos : ∀ i, 0 < l i)
    (horder : ∀ i j, i < j → u i < l j)
    (hold : ∀ i, (l i = u i ∧ P.IsRoot (-l i)) ∨
      (l i < u i ∧ P.eval (-l i) * P.eval (-u i) < 0))
    (hsLeft : ∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * Q.eval (-l i))
    (hsRight : ∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * Q.eval (-u i)) :
    ∃ (old : Fin m → ℝ) (next : Fin (m + 1) → ℝ),
      CompleteNegativeRoots P old ∧ CompleteNegativeRoots Q next ∧
        ∀ i, next i.castSucc < l i ∧ l i ≤ old i ∧ old i ≤ u i ∧ u i < next i.succ := by
  classical
  have hchoose (i : Fin m) : ∃ r, l i ≤ r ∧ r ≤ u i ∧ P.IsRoot (-r) := by
    rcases hold i with ⟨heq, hroot⟩ | ⟨hlt, hs⟩
    · exact ⟨l i, le_rfl, heq.le, hroot⟩
    · have hsign : (P.comp (-X)).eval (l i) * (P.comp (-X)).eval (u i) < 0 := by
        simpa [eval_comp] using hs
      obtain ⟨r, hl, hu, hr⟩ := AlternatingSignRoots.root_between hlt hsign
      exact ⟨r, hl.le, hu.le, by simpa [Polynomial.IsRoot, eval_comp] using hr⟩
  choose old hroot using hchoose
  have hOldMono : StrictMono old := fun i j hij =>
    (hroot i).2.1.trans_lt ((horder i j hij).trans_le (hroot j).1)
  have hOldComplete : CompleteNegativeRoots P old :=
    ⟨hdegP, hOldMono, fun i => (hpos i).trans_le (hroot i).1,
      AlternatingSignRoots.roots_of_complete_list P (fun i => -old i) hdegP hP
        (neg_injective.comp hOldMono.injective) (fun i => (hroot i).2.2)⟩
  have hl (i : Fin m) : l i ≤ u i := (hroot i).1.trans (hroot i).2.1
  have hLeftMono : StrictMono l := fun i j hij => (hl i).trans_lt (horder i j hij)
  have hRightMono : StrictMono u := fun i j hij => (horder i j hij).trans_le (hl j)
  obtain ⟨next, hNextComplete, hNextLeft⟩ :=
    roots_of_signed_test_points Q l hdegQ (Or.inr rfl) hLeftMono hpos hzero hlead hsLeft
  obtain ⟨next', hNextComplete', hNextRight⟩ :=
    roots_of_signed_test_points Q u hdegQ (Or.inr rfl) hRightMono
      (fun i => (hpos i).trans_le (hl i)) hzero hlead hsRight
  -- The two endpoint arrays isolate the same complete ordered list for Q.
  rw [hNextComplete'.unique hNextComplete] at hNextRight
  exact ⟨old, next, hOldComplete, hNextComplete, fun i =>
    ⟨hNextLeft.1 i i.castSucc rfl, (hroot i).1, (hroot i).2.1, hNextRight.2 i i.succ rfl⟩⟩

end OpenMathResearch.LongCycleExcedances
