import RepositoryQuotientShape
import RationalPointSound

namespace RepositoryQuotientAudit

open LongCycles Polynomial
open OpenMathResearch.LongCycleExcedances

/-- Both sides use the same Fin-labelled permutations, return cutoff and
strict excedances. Classical decidability is shared by the definitions. -/
theorem canonical_eq_external_divX (n k : ℕ) :
    canonicalReducedRow n k = (enumerator n k).divX := rfl

/-- Exact signed endpoint readout of the quotient of the original enumerator.
The rational inputs can be read directly from a separating-point witness. -/
theorem original_signed_point_of_rational_margin (n k W : ℕ)
    (hn : 0 < n) (hk : 2 ≤ k) {y σ : ℚ}
    (hy : 0 ≤ y) (hσ : |σ| = 1)
    (hq : rationalTailRatio n W y < 1)
    (hm : rationalTailBound n W y <
      σ * rationalPrefixEval (cycleQuotientCoeff exactEulerianCoeff n k) W y) :
    0 < (σ : ℝ) * ((enumerator n k).divX).eval (-(y : ℝ)) := by
  rw [← canonical_eq_external_divX]
  apply signed_canonical_of_rational_margin n k W hk (cycleQuotientCoeff exactEulerianCoeff n k)
    _ hy hσ hq hm
  intro j
  rw [canonical_eq_external_divX]
  exact exact_coeff_eq_divX n k j hn hk

end RepositoryQuotientAudit

#print axioms RepositoryQuotientAudit.canonical_eq_external_divX
#print axioms RepositoryQuotientAudit.original_signed_point_of_rational_margin
