import RepositoryActualRationalPoint
import StrictRootListTranslation
import LongCycleFinite.Assembly

namespace RepositoryQuotientAudit

open Polynomial LongCycles LongCycleFinite
open OpenMathResearch.LongCycleExcedances
open OpenMathResearch.OrientedNegativeInterlace

/-- Convert complete increasing moduli into the supplying release's exact
ordered real factorization predicate. -/
theorem strict_of_complete_moduli {d : ℕ} {P Q : ℝ[X]}
    {r : Fin d → ℝ} {s : Fin (d + 1) → ℝ}
    (hp : P ≠ 0) (hq : Q ≠ 0)
    (hr : CompleteNegativeRoots P r) (hs : CompleteNegativeRoots Q s)
    (h : ∀ i, s i.castSucc < r i ∧ r i < s i.succ) :
    StrictNegativeInterlacing P Q d := by
  refine ⟨(fun i => -r i.rev), (fun i => -s i.rev),
    leadingCoeff_ne_zero.mpr hp, leadingCoeff_ne_zero.mpr hq,
    complete_moduli_factorization hr, complete_moduli_factorization hs,
    negative_reversed_mono hr.2.1, negative_reversed_mono hs.2.1, ?_, ?_, ?_⟩
  · intro i
    exact neg_lt_zero.mpr (hr.2.2.1 i.rev)
  · intro i
    exact neg_lt_zero.mpr (hs.2.2.1 i.rev)
  · exact negative_reversed_interlaces h

theorem original_weak_of_complete_moduli {n k : ℕ} (hk : 2 ≤ k) (hn : k ≤ n)
    {r : Fin (n - 2) → ℝ} {s : Fin (n - 2 + 1) → ℝ}
    (hr : CompleteNegativeRoots (enumerator n k).divX r)
    (hs : CompleteNegativeRoots (enumerator (n + 1) k).divX s)
    (h : ∀ i, s i.castSucc < r i ∧ r i < s i.succ) :
    WeakRealInterlacing (enumerator n k) (enumerator (n + 1) k) := by
  have hfactor (m : ℕ) (hpos : 0 < m) :
      enumerator m k = X * (enumerator m k).divX :=
    (LongCycleBounds.Band.actual_general_cycle_row hk hpos).trans
      (congrArg (fun P : ℝ[X] => X * P) (generalCycleQuotient_eq_divX m k hpos hk))
  have hw := weak_mul_X_of_strict (strict_of_complete_moduli
    (original_divX_shape hk hn).2.1.ne_zero
    (original_divX_shape hk (by omega : k ≤ n + 1)).2.1.ne_zero hr hs h)
  rw [← hfactor n (by omega), ← hfactor (n + 1) (by omega)] at hw
  exact hw

/-- Complete mixed windows for the consecutive reduced rows imply the exact
original weak-interlacing predicate after adjoining the shared zero. -/
theorem original_weak_of_mixed_windows {n k : ℕ} (hk : 2 ≤ k) (hn : k ≤ n) :
    let P := (enumerator n k).divX
    let Q := (enumerator (n + 1) k).divX
    ∀ (l u : Fin (n - 2) → ℝ)
    (_hpos : ∀ i, 0 < l i) (_horder : ∀ i j, i < j → u i < l j)
    (_hold : ∀ i, (l i = u i ∧ P.IsRoot (-l i)) ∨
      (l i < u i ∧ P.eval (-l i) * P.eval (-u i) < 0))
    (_hsLeft : ∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * Q.eval (-l i))
    (_hsRight : ∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * Q.eval (-u i)),
    WeakRealInterlacing (enumerator n k) (enumerator (n + 1) k) := by
  dsimp only
  intro l u hpos horder hold hsLeft hsRight
  obtain ⟨hdP, hmonicP, _⟩ := original_divX_shape hk hn
  obtain ⟨hdQ, hmonicQ, hzeroQ⟩ := original_divX_shape hk (by omega : k ≤ n + 1)
  have hdQ' : (enumerator (n + 1) k).divX.natDegree = n - 2 + 1 := by omega
  have hzero : 0 < (enumerator (n + 1) k).divX.eval 0 := by rw [hzeroQ]; norm_num
  have hlead : 0 < (enumerator (n + 1) k).divX.leadingCoeff := by
    rw [hmonicQ.leadingCoeff]
    norm_num
  obtain ⟨r, s, hr, hs, h⟩ := interlace_of_mixed_root_witnesses l u
    hmonicP.ne_zero hdP hdQ' hzero hlead hpos horder hold hsLeft hsRight
  exact original_weak_of_complete_moduli hk hn hr hs (fun i =>
    ⟨(h i).1.trans_le (h i).2.1, (h i).2.2.1.trans_lt (h i).2.2.2⟩)

end RepositoryQuotientAudit

#print axioms RepositoryQuotientAudit.strict_of_complete_moduli
#print axioms RepositoryQuotientAudit.original_weak_of_complete_moduli
#print axioms RepositoryQuotientAudit.original_weak_of_mixed_windows
