import MonomialTiltBounds
import LongCycleBounds.BandMoments

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open scoped Real

/-- The linear coefficient of the original cutoff logarithm is the logistic
value at zero. -/
theorem original_cutoff_log_linear (k : ℕ) (s : ℝ) :
    (RepositoryQuotientAudit.cutoffLogCoefficient k (-Real.exp (-s)) 1 : ℂ) =
      Complex.exp (-(s : ℂ)) / (1 + Complex.exp (-(s : ℂ))) := by
  unfold RepositoryQuotientAudit.cutoffLogCoefficient
  rw [if_pos (show (1:ℕ) = 1 from rfl)]
  simp only [neg_neg, sub_neg_eq_add,
    Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_exp, Complex.ofReal_neg]

/-- Each nonlinear coefficient retained by the original cutoff logarithm
is minus the full odd-pole sum after multiplying by its degree. -/
theorem original_cutoff_log_poles {k j : ℕ} (hj : 2 ≤ j) (hjk : j < k)
    {s : ℝ} (hs : 0 ≤ s) :
    (j : ℂ) * (RepositoryQuotientAudit.cutoffLogCoefficient k (-Real.exp (-s)) j : ℂ) =
      -(∑' l : ℤ, 1 / ((s : ℂ) + (2 * (l : ℂ) + 1) * π * Complex.I) ^ j) := by
  have h1 : j ≠ 1 := by omega
  have hfac : j.factorial = j * (j-1).factorial := by
    have hj' : j-1+1 = j := by omega
    conv_lhs => rw [← hj']
    rw [Nat.factorial_succ, hj']
  have hj0 : (j : ℂ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have hf0 : ((j-1).factorial : ℂ) ≠ 0 := by exact_mod_cast (j-1).factorial_ne_zero
  unfold RepositoryQuotientAudit.cutoffLogCoefficient
  rw [if_neg h1, if_pos (show 2 ≤ j ∧ j < k from ⟨hj,hjk⟩)]
  push_cast
  change (j : ℂ) * (-(LongCycleBounds.Band.moment j (-Real.exp (-s)) : ℂ) /
    (j.factorial : ℂ)) = -LongCycleBounds.oddPoleSum j s
  rw [LongCycleBounds.Band.moment_poles j hj s hs, hfac, Nat.cast_mul]
  field_simp [hj0,hf0]
  ring

#print axioms original_cutoff_log_linear
#print axioms original_cutoff_log_poles
end OpenMathResearch.LongCycleExcedances
