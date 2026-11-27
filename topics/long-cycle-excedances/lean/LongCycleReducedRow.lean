import LongCycleRunColors
import LongCyclePrefixTail
import Mathlib.Algebra.Polynomial.Inductions

namespace OpenMathResearch.LongCycleExcedances

open Polynomial RunColors

/-- The original row with its initial factor of `X` removed. -/
noncomputable def canonicalReducedRow (n k : ℕ) : ℝ[X] :=
  (originalEnumerator n k).divX

theorem original_eq_X_mul_canonical (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) :
    originalEnumerator n k = X * canonicalReducedRow n k := by
  obtain ⟨hl, hu⟩ := original_coeff_envelope n k 0 hk
  simp only [Nat.cast_zero, zero_pow hn.ne'] at hu
  have hz := le_antisymm hu hl
  simpa only [canonicalReducedRow, hz, C_0, add_zero] using
    (X_mul_divX_add (originalEnumerator n k)).symm

/-- Any polynomial supplied by a checked factorization is the canonical quotient. -/
theorem eq_canonical_of_factor {n k : ℕ} {P : ℝ[X]}
    (h : originalEnumerator n k = X * P) :
    P = canonicalReducedRow n k := by
  ext j
  simp only [canonicalReducedRow, coeff_divX, h, coeff_X_mul]

theorem canonical_coeff_envelope (n k j : ℕ) (hk : 2 ≤ k) :
    0 ≤ (canonicalReducedRow n k).coeff j ∧
    (canonicalReducedRow n k).coeff j ≤ ((j : ℝ) + 1) ^ n := by
  simpa only [canonicalReducedRow, coeff_divX, Nat.cast_add, Nat.cast_one] using
    original_coeff_envelope n k (j + 1) hk

/-- The coefficient envelope for the interval certificate follows from the original
permutation definition. Only the numerical tail and Horner margins remain. -/
theorem canonical_signed_pos_on_window_of_horner (n k W : ℕ) (hk : 2 ≤ k)
    {a b B σ : ℝ} (ha : 0 ≤ a) (hb : b ≤ B) (hq : tailRatio n W B < 1)
    (hσ : |σ| = 1)
    (hmargin : tailBound n W B <
      (intervalHorner a b W (fun j => σ * ((-1 : ℝ) ^ j *
        (canonicalReducedRow n k).coeff j))).1) :
    ∀ y ∈ Set.Icc a b, 0 < σ * (canonicalReducedRow n k).eval (-y) :=
  signed_pos_on_window_of_horner _ n W ha hb hq
    (fun j _ => canonical_coeff_envelope n k j hk) hσ hmargin

/-- Actual adjacent rows satisfy the tails required by the mixed witness criterion. -/
theorem canonical_interlace_of_prefix_and_mixed_witnesses {m n k W : ℕ}
    (hk : 2 ≤ k) :
    let P := canonicalReducedRow n k
    let Q := canonicalReducedRow (n + 1) k
    ∀ (l u : Fin m → ℝ) (_hP : P ≠ 0) (_hdegP : P.natDegree = m)
    (_hdegQ : Q.natDegree = m + 1) (_hzero : 0 < Q.eval 0)
    (_hlead : 0 < Q.leadingCoeff) (_hpos : ∀ i, 0 < l i)
    (_horder : ∀ i j, i < j → u i < l j)
    (_hold : ∀ i, (l i = u i ∧ P.IsRoot (-l i)) ∨
      (l i < u i ∧ (P.eval (-l i) * P.eval (-u i) < 0 ∨
        (PrefixMargin P n W (l i) ((-1 : ℝ) ^ i.val) ∧
          PrefixMargin P n W (u i) (-((-1 : ℝ) ^ i.val))))))
    (_hsLeft : ∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * Q.eval (-l i) ∨
      PrefixMargin Q (n + 1) W (l i) ((-1 : ℝ) ^ (i.val + 1)))
    (_hsRight : ∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * Q.eval (-u i) ∨
      PrefixMargin Q (n + 1) W (u i) ((-1 : ℝ) ^ (i.val + 1))),
    ∃ (old : Fin m → ℝ) (next : Fin (m + 1) → ℝ),
      OrientedNegativeInterlace.CompleteNegativeRoots P old ∧
      OrientedNegativeInterlace.CompleteNegativeRoots Q next ∧
      ∀ i, next i.castSucc < l i ∧ l i ≤ old i ∧ old i ≤ u i ∧ u i < next i.succ := by
  dsimp only
  intro l u hP hdegP hdegQ hzero hlead hpos horder hold hsLeft hsRight
  exact interlace_of_prefix_and_mixed_witnesses l u hP hdegP hdegQ hzero hlead hpos horder
    (fun j _ => canonical_coeff_envelope n k j hk)
    (fun j _ => canonical_coeff_envelope (n + 1) k j hk) hold hsLeft hsRight

#print axioms canonical_interlace_of_prefix_and_mixed_witnesses
#print axioms original_eq_X_mul_canonical
#print axioms eq_canonical_of_factor
#print axioms canonical_signed_pos_on_window_of_horner

end OpenMathResearch.LongCycleExcedances
