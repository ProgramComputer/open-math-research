import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OpenMathResearch.LongCycleExcedances.RelativeMargins
open Polynomial Finset

/-- Coefficientwise relative errors preserve a signed value whenever the
margin exceeds the maximal absolute perturbation of the evaluation. -/
theorem sign_under_relative_perturbations (P Q : ℝ[X]) (ε y σ : ℝ)
    (hy : 0 ≤ y) (hs : |σ| = 1)
    (error : ∀ j, |Q.coeff j - P.coeff j| ≤ ε * P.coeff j)
    (margin : ε * P.eval y < σ * P.eval (-y)) :
    0 < σ * Q.eval (-y) := by
  let M := max P.natDegree Q.natDegree + 1
  have hP : P.natDegree < M := by dsimp [M]; omega
  have hQ : Q.natDegree < M := by dsimp [M]; omega
  have h : |Q.eval (-y) - P.eval (-y)| ≤ ε * P.eval y := by
    rw [Q.eval_eq_sum_range' hQ, P.eval_eq_sum_range' hP, P.eval_eq_sum_range' hP,
      ← sum_sub_distrib, mul_sum]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro j _
    rw [← sub_mul, abs_mul, abs_pow, abs_neg, abs_of_nonneg hy, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (error j) (pow_nonneg hy _)
  have h' : |σ * (Q.eval (-y)-P.eval (-y))| ≤ ε * P.eval y := by simpa [abs_mul, hs] using h
  have lo := (abs_le.mp h').1
  linarith [show σ * (Q.eval (-y)-P.eval (-y))=σ * Q.eval (-y)-σ * P.eval (-y) by ring]

theorem reflected_coeff (P : ℝ[X]) (j : ℕ) :
    (P.comp (-X)).coeff j = (-1 : ℝ)^j * P.coeff j := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp [add_comp, hP, hQ, mul_add]
  | monomial n a =>
    have he : -(X:ℝ[X]) = C (-1 : ℝ)*X := by simp
    rw [monomial_comp, he, mul_pow, ← C_pow, ← mul_assoc, ← C_mul, C_mul_X_pow_eq_monomial]
    by_cases h : n=j
    · subst n
      simp [mul_comm]
    · simp [coeff_monomial, h, Ne.symm h]

/-- The relative error bound is attained by a real coefficient perturbation. -/
theorem attainable_perturbation (P : ℝ[X]) (ε y σ : ℝ) (he : 0 ≤ ε) (hs : |σ| = 1)
    (hn : ∀ j, 0 ≤ P.coeff j) :
    ∃ Q : ℝ[X], (∀ j, |Q.coeff j - P.coeff j| = ε * P.coeff j) ∧
      σ * Q.eval (-y) = σ * P.eval (-y) - ε * P.eval y := by
  refine ⟨P - C (σ * ε) * (P.comp (-X)), ?_, ?_⟩
  · intro j
    rw [coeff_sub, coeff_C_mul, reflected_coeff]
    have h : P.coeff j - σ * ε * ((-1 : ℝ)^j * P.coeff j) - P.coeff j =
        -(σ * ε * ((-1 : ℝ)^j * P.coeff j)) := by ring
    rw [h, abs_neg, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, hs,
      abs_of_nonneg he, abs_of_nonneg (hn j), one_pow, one_mul, one_mul]
  · have hsq : σ * σ=1 := by nlinarith [sq_abs σ, hs]
    simp only [eval_sub, eval_mul, eval_C, eval_comp, eval_neg, eval_X, neg_neg]
    calc
      _ = σ * P.eval (-y) - (σ * σ) * ε * P.eval y := by ring
      _ = _ := by rw [hsq, one_mul]

#print axioms attainable_perturbation
#print axioms sign_under_relative_perturbations
end OpenMathResearch.LongCycleExcedances.RelativeMargins
