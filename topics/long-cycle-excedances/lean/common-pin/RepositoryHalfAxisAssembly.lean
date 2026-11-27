import RepositoryRootAssembly
import ReciprocalHalfWindows

namespace RepositoryQuotientAudit
open LongCycles LongCycleBounds.Band Polynomial
open OpenMathResearch.LongCycleExcedances

/-- The frozen quotient reciprocity identity for the canonical shift of the
literal enumerator. -/
theorem original_divX_reciprocity {n k : ℕ} (hk : 2 ≤ k) (hn : 0 < n)
    (t : ℝ) (ht : t ≠ 0) :
    t^(n-2) * (enumerator n k).divX.eval t⁻¹ = (enumerator n k).divX.eval t := by
  rw [← generalCycleQuotient_eq_divX n k hn hk]
  exact generalCycleQuotient_reciprocity hk ht

/-- Left-half mixed witnesses and the odd central next sign suffice for the
literal weak-interlacing claim on the consecutive original rows. -/
theorem original_weak_of_half_axis_windows {n k : ℕ} (hk : 2 ≤ k) (hn : k ≤ n) :
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
    WeakRealInterlacing (enumerator n k) (enumerator (n + 1) k) := by
  dsimp only
  intro l u hpos hbelow horder hold hsLeft hsRight hcenter
  have hrP := original_divX_reciprocity (n := n) hk (by omega)
  have hrQ := original_divX_reciprocity (n := n + 1) hk (by omega)
  have he : n + 1 - 2 = (n - 2) + 1 := by omega
  rw [he] at hrQ
  obtain ⟨L, U, hL, hLU, hroot, hsL, hsU⟩ :=
    mixed_witnesses_of_reciprocal_half hrP hrQ l u hpos hbelow horder hold hsLeft hsRight hcenter
  exact original_weak_of_mixed_windows hk hn L U hL hLU hroot hsL hsU

end RepositoryQuotientAudit

#print axioms RepositoryQuotientAudit.original_divX_reciprocity
#print axioms RepositoryQuotientAudit.original_weak_of_half_axis_windows
