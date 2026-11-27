import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Polynomial

/-- Coefficient bound for P(-v)/v^h throughout a positive closed interval.
The lower endpoint controls negative relative powers and the upper controls
nonnegative relative powers. -/
def frontCoefficientNorm (P : ℝ[X]) (h : ℕ) (L U : ℝ) : ℝ :=
  ∑ j ∈ P.support, |P.coeff j| * (if h ≤ j then U^(j-h) else 1/L^(h-j))

theorem front_coefficient_bound (P : ℝ[X]) {h : ℕ} {L U v : ℝ}
    (hL : 0 < L) (hv : L ≤ v) (hU : v ≤ U) :
    |P.eval (-v)| ≤ frontCoefficientNorm P h L U * v^h := by
  have hv' := hL.trans_le hv
  have hmon (j : ℕ) :
      v^j ≤ (if h ≤ j then U^(j-h) else 1/L^(h-j))*v^h := by
    split_ifs with hj
    · simpa only [←pow_add,Nat.sub_add_cancel hj] using
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hv'.le hU (j-h)) (pow_nonneg hv'.le h)
    · rw [one_div, inv_mul_eq_div, le_div_iff₀ (pow_pos hL _)]
      simpa only [←pow_add,Nat.add_sub_of_le (Nat.le_of_not_ge hj)] using
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL.le hv (h-j)) (pow_nonneg hv'.le j)
  rw [Polynomial.eval_eq_sum,Polynomial.sum,frontCoefficientNorm,sum_mul]
  calc
    _ ≤ ∑ j ∈ P.support, |P.coeff j*(-v)^j| := abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro j _
      rw [abs_mul,abs_pow,abs_neg,abs_of_pos hv',mul_assoc]
      exact mul_le_mul_of_nonneg_left (hmon j) (abs_nonneg _)

#print axioms front_coefficient_bound
end OpenMathResearch.LongCycleExcedances
