import CycleProbabilityBands
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace OpenMathResearch.LongCycleExcedances.CycleProbability
open Polynomial Finset

/-- The factorially normalized original polynomial at 1. The anchored
recurrence has the same shape as the literal permutation recurrence. -/
theorem from_anchored_polynomials {k : ℕ} (hk : 0 < k)
    (E A : ℕ → ℝ[X]) (hzero : E 0 = 1)
    (heuler : ∀ m, (A m).eval 1 = (m.factorial : ℝ))
    (hrec : ∀ r, 0 < r → E r = ∑ a ∈ Icc k r,
      C ((r-1).choose (a-1) : ℝ) * (X * A (a-1)) * E (r-a)) :
    Spec k (fun r => (E r).eval 1 / (r.factorial : ℝ)) := by
  apply from_anchored_counts hk (fun r => (E r).eval 1)
  · simp [hzero]
  · intro r rp rs
    have emp : Icc k r = ∅ := Finset.Icc_eq_empty (not_le_of_gt rs)
    rw [hrec r rp, emp, sum_empty, eval_zero]
  · intro r hr
    have rp : 0 < r := by omega
    have h := congrArg (fun p : ℝ[X] => p.eval 1) (hrec r rp)
    simpa only [eval_finsetSum, eval_mul, eval_C, eval_X, one_mul, heuler] using h

#print axioms from_anchored_polynomials
end OpenMathResearch.LongCycleExcedances.CycleProbability
