import LongCycleReducedRow
import Mathlib.Algebra.Order.Field.Rat

namespace OpenMathResearch.LongCycleExcedances
open Polynomial Finset

/-- Exact retained evaluation for a coefficient provider. -/
def rationalPrefixEval (c : ℕ → ℚ) (W : ℕ) (y : ℚ) : ℚ :=
  ∑ j ∈ range W, c j * (-y) ^ j

def rationalTailRatio (n W : ℕ) (y : ℚ) : ℚ :=
  y * (((W : ℚ) + 2) / ((W : ℚ) + 1)) ^ n

def rationalTailBound (n W : ℕ) (y : ℚ) : ℚ :=
  ((W : ℚ) + 1) ^ n * y ^ W / (1 - rationalTailRatio n W y)

theorem rationalPrefixEval_cast {P : ℝ[X]} {c : ℕ → ℚ}
    (hc : ∀ j, (c j : ℝ) = P.coeff j) (W : ℕ) (y : ℚ) :
    (rationalPrefixEval c W y : ℝ) = prefixEval P W y := by
  unfold rationalPrefixEval prefixEval
  push_cast
  simp only [hc]

theorem rationalTailRatio_cast (n W : ℕ) (y : ℚ) :
    (rationalTailRatio n W y : ℝ) = tailRatio n W y := by
  unfold rationalTailRatio tailRatio
  push_cast
  rfl

theorem rationalTailBound_cast (n W : ℕ) (y : ℚ) :
    (rationalTailBound n W y : ℝ) = tailBound n W y := by
  unfold rationalTailBound tailBound
  push_cast
  rw [rationalTailRatio_cast]

/-- A rational endpoint sign certificate for a canonical original row. The
coefficient provider is identified separately with this row. -/
theorem signed_canonical_of_rational_margin (n k W : ℕ) (hk : 2 ≤ k)
    (c : ℕ → ℚ) (hc : ∀ j, (c j : ℝ) = (canonicalReducedRow n k).coeff j)
    {y σ : ℚ} (hy : 0 ≤ y) (hσ : |σ| = 1)
    (hq : rationalTailRatio n W y < 1)
    (hm : rationalTailBound n W y < σ * rationalPrefixEval c W y) :
    0 < (σ : ℝ) * (canonicalReducedRow n k).eval (-(y : ℝ)) := by
  apply signed_eval_pos_of_prefix_margin _ n W (by exact_mod_cast hy) le_rfl
  · rw [← rationalTailRatio_cast]
    exact_mod_cast hq
  · exact fun j _ => canonical_coeff_envelope n k j hk
  · exact_mod_cast hσ
  · rw [← rationalTailBound_cast, ← rationalPrefixEval_cast hc]
    exact_mod_cast hm

#print axioms signed_canonical_of_rational_margin
end OpenMathResearch.LongCycleExcedances
