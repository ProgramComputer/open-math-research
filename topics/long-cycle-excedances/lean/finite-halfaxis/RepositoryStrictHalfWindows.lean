import RepositoryHalfAxisAssembly

namespace RepositoryQuotientAudit
open Polynomial LongCycles LongCycleFinite LongCycleBounds.Band
open OpenMathResearch.LongCycleExcedances

/-- A complete set of signed half-axis windows supplies strict interlacing for
the two reduced rows and weak interlacing for the original permutation rows. -/
theorem original_strict_and_weak_of_half_axis_windows {n k : ℕ} (hk : 2 ≤ k) (hn : k ≤ n) :
    let P := (enumerator n k).divX
    let Q := (enumerator (n + 1) k).divX
    ∀ (l u : Fin ((n - 2) / 2) → ℝ)
    (_hpos : ∀ i, 0 < l i) (_hbelow : ∀ i, u i < 1)
    (_horder : ∀ i j, i < j → u i < l j)
    (_hold : ∀ i, (l i = u i ∧ P.IsRoot (-l i)) ∨
      (l i < u i ∧ P.eval (-l i) * P.eval (-u i) < 0))
    (_hsLeft : ∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * Q.eval (-l i))
    (_hsRight : ∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * Q.eval (-u i))
    (_hcenter : Odd (n - 2) → 0 < (-1 : ℝ)^((n - 2) / 2 + 1) * Q.eval (-1)),
    StrictNegativeInterlacing P Q (n-2) ∧
      WeakRealInterlacing (enumerator n k) (enumerator (n + 1) k) := by
  dsimp only
  intro l u hpos hbelow horder hold hsLeft hsRight hcenter
  have hrP := original_divX_reciprocity (n := n) hk (by omega)
  have hrQ := original_divX_reciprocity (n := n + 1) hk (by omega)
  have he : n + 1 - 2 = (n - 2) + 1 := by omega
  rw [he] at hrQ
  obtain ⟨L, U, hL, hLU, hroot, hsL, hsU⟩ :=
    mixed_witnesses_of_reciprocal_half hrP hrQ l u hpos hbelow horder hold hsLeft hsRight hcenter
  obtain ⟨hdP, hmP, _⟩ := original_divX_shape hk hn
  obtain ⟨hdQ, hmQ, hzero⟩ := original_divX_shape hk (by omega : k ≤ n+1)
  have hdQ' : (enumerator (n+1) k).divX.natDegree = n-2+1 := hdQ.trans he
  have hposQ : 0 < (enumerator (n+1) k).divX.eval 0 := by rw [hzero]; norm_num
  have hlead : 0 < (enumerator (n+1) k).divX.leadingCoeff := by rw [hmQ.leadingCoeff]; norm_num
  obtain ⟨r, s, hr, hs, h⟩ := interlace_of_mixed_root_witnesses L U
    hmP.ne_zero hdP hdQ' hposQ hlead hL hLU hroot hsL hsU
  have hstrict (i : Fin (n-2)) : s i.castSucc < r i ∧ r i < s i.succ :=
    ⟨(h i).1.trans_le (h i).2.1, (h i).2.2.1.trans_lt (h i).2.2.2⟩
  exact ⟨strict_of_complete_moduli hmP.ne_zero hmQ.ne_zero hr hs hstrict,
    original_weak_of_complete_moduli hk hn hr hs hstrict⟩

#print axioms original_strict_and_weak_of_half_axis_windows
end RepositoryQuotientAudit
