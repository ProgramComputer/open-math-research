import CoefficientFrontWindow
import Mathlib.Algebra.Polynomial.Derivative

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Polynomial

def frontCoefficientWeight (h : ℕ) (L U : ℝ) (j : ℕ) : ℝ :=
  if h ≤ j then U^(j-h) else 1/L^(h-j)

private theorem wt_nonneg {h j : ℕ} {L U : ℝ} (hL : 0 < L) (hU : 0 ≤ U) :
    0 ≤ frontCoefficientWeight h L U j := by
  unfold frontCoefficientWeight
  split <;> positivity

private theorem wt_succ {h j : ℕ} {L U : ℝ} (hL : 0 < L) (hLU : L ≤ U) :
    frontCoefficientWeight h L U (j+1) ≤ U * frontCoefficientWeight h L U j := by
  have hU := hL.trans_le hLU
  unfold frontCoefficientWeight
  by_cases hj : h ≤ j
  · rw [if_pos (by omega : h ≤ j+1), if_pos hj,
      show j+1-h = j-h+1 by omega, pow_succ, mul_comm]
  · rw [if_neg hj]
    have hs : h-j = h-(j+1)+1 := by omega
    by_cases hj' : h ≤ j+1
    · rw [if_pos hj', show j+1-h=0 by omega, pow_zero, show h-j=1 by omega, pow_one]
      rw [mul_one_div]
      exact (le_div_iff₀ hL).2 (by simpa using hLU)
    · rw [if_neg hj', hs, pow_succ, mul_one_div]
      apply (le_div_iff₀ (mul_pos (pow_pos hL _) hL)).2
      rw [←mul_assoc, one_div_mul_cancel (pow_ne_zero _ hL.ne'), one_mul]
      exact hLU

private theorem norm_on_superset (P : ℝ[X]) {s : Finset ℕ} (hs : P.support ⊆ s)
    (h : ℕ) (L U : ℝ) :
    frontCoefficientNorm P h L U = ∑ j ∈ s, |P.coeff j| * frontCoefficientWeight h L U j := by
  unfold frontCoefficientNorm
  apply sum_subset hs
  intro j _ hj
  have hz : P.coeff j = 0 := by
    by_contra h
    exact hj (mem_support_iff.mpr h)
  simp [hz]

theorem front_norm_monomial (a : ℝ) (j h : ℕ) (L U : ℝ) :
    frontCoefficientNorm (C a*X^j) h L U = |a| * frontCoefficientWeight h L U j := by
  have hs : (C a*X^j : ℝ[X]).support ⊆ {j} := by
    intro i hi
    apply mem_singleton.mpr
    by_contra he
    exact (mem_support_iff.mp hi) (by rw [coeff_C_mul_X_pow, if_neg he])
  rw [norm_on_superset _ hs, sum_singleton, coeff_C_mul_X_pow, if_pos rfl]

theorem front_norm_add_le (P Q : ℝ[X]) (h : ℕ) {L U : ℝ} (hL : 0 < L) (hU : 0 ≤ U) :
    frontCoefficientNorm (P+Q) h L U ≤
      frontCoefficientNorm P h L U + frontCoefficientNorm Q h L U := by
  let s := P.support ∪ Q.support
  rw [norm_on_superset (P+Q) (show (P+Q).support ⊆ s from support_add),
      norm_on_superset P (show P.support ⊆ s from subset_union_left),
      norm_on_superset Q (show Q.support ⊆ s from subset_union_right), ←sum_add_distrib]
  apply sum_le_sum
  intro j _
  rw [coeff_add, ←add_mul]
  exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (wt_nonneg hL hU)

theorem front_norm_neg (P : ℝ[X]) (h : ℕ) (L U : ℝ) :
    frontCoefficientNorm (-P) h L U = frontCoefficientNorm P h L U := by
  simp [frontCoefficientNorm, support_neg]

theorem front_norm_X_mul_le (P : ℝ[X]) (h : ℕ) {L U : ℝ} (hL : 0 < L) (hLU : L ≤ U) :
    frontCoefficientNorm (X*P) h L U ≤ U * frontCoefficientNorm P h L U := by
  have hs : (X*P).support ⊆ P.support.image Nat.succ := by
    intro j hj
    cases j with
    | zero => simp [mem_support_iff] at hj
    | succ j =>
      exact mem_image.mpr ⟨j, mem_support_iff.mpr (by simpa [coeff_X_mul] using mem_support_iff.mp hj), rfl⟩
  rw [norm_on_superset (X*P) hs, sum_image (fun _ _ _ _ he => Nat.succ.inj he)]
  change (∑ j ∈ P.support, |(X*P).coeff (j+1)| * frontCoefficientWeight h L U (j+1)) ≤ _
  rw [frontCoefficientNorm, mul_sum]
  apply sum_le_sum
  intro j _
  rw [coeff_X_mul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (wt_succ hL hLU) (abs_nonneg _)

theorem front_norm_closed_successor (D V : ℝ[X]) {h : ℕ} {L U a : ℝ}
    (hL : 0 < L) (hLU : L ≤ U) (hU : U ≤ 1/2) (ha : 0 < a)
    (hD : frontCoefficientNorm D h L U ≤ 3/20*a)
    (hV : frontCoefficientNorm V h L U ≤ 18/25*a) :
    frontCoefficientNorm ((1-X)*D+V) h L U < a := by
  have hm := front_norm_add_le ((1-X)*D) V h hL (hL.trans_le hLU).le
  have hDX := front_norm_add_le D (-(X*D)) h hL (hL.trans_le hLU).le
  rw [←sub_eq_add_neg, front_norm_neg] at hDX
  rw [sub_mul, one_mul] at hm ⊢
  have hs := front_norm_X_mul_le D h hL hLU
  have hd := mul_le_mul_of_nonneg_left hD (hL.trans_le hLU).le
  have hu := mul_le_mul_of_nonneg_right hU (show 0 ≤ 3/20*a by positivity)
  linarith

/-- The insertion identity turns the certificate residual into the centered
derivative and the full lag polynomial. -/
theorem front_next_residual_eq (P Q V : ℝ[X]) (h : ℕ) (a n : ℝ)
    (hq : Q = C n*X*P+(1-X)*(X*P.derivative)+V) :
    frontNextResidual P Q (C n*X+(1-X)*C ((h:ℝ)+1)) h a =
      (1-X)*(X*P.derivative-C ((h:ℝ)+1)*P+C a*X^h)+V := by
  rw [frontNextResidual,hq]
  ring

#print axioms front_norm_closed_successor
#print axioms front_next_residual_eq
end OpenMathResearch.LongCycleExcedances
