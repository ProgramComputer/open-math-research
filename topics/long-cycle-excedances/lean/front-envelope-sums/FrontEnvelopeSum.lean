import FrontFiniteSums

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Polynomial

def frontCenteredDerivative (P : ℝ[X]) (h : ℕ) (a : ℝ) : ℝ[X] :=
  X*P.derivative-C ((h:ℝ)+1)*P+C a*X^h

private theorem front_old_coeff (P : ℝ[X]) (h j : ℕ) (a u : ℝ) :
    (frontOldResidual P h a u).coeff j =
      P.coeff j - ((if j=h then a else 0)+(if j=h+1 then a/u else 0)) := by
  have he : C a*X^h*(1+C (1/u)*X) = (C a*X^h+C (a/u)*X^(h+1) : ℝ[X]) := by
    rw [mul_add,mul_one,pow_succ, show a/u=a*(1/u) by ring, C_mul]
    ring
  rw [frontOldResidual,he,coeff_sub,coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X_pow]

private theorem front_deriv_coeff (P : ℝ[X]) (h j : ℕ) (a : ℝ) :
    (frontCenteredDerivative P h a).coeff j =
      ((j:ℝ)-((h:ℝ)+1))*P.coeff j+(if j=h then a else 0) := by
  have he : (X*P.derivative).coeff j = (j:ℝ)*P.coeff j := by
    cases j with
    | zero => simp
    | succ j => rw [coeff_X_mul, coeff_derivative]; simp [Nat.cast_succ, mul_comm]
  rw [frontCenteredDerivative, coeff_add, coeff_C_mul_X_pow, coeff_sub, coeff_C_mul, he]
  ring

private theorem linear_rank_bound (l : ℕ) : (l:ℝ)+1 ≤ 2^l := by
  induction l with
  | zero => norm_num
  | succ l h =>
    rw [Nat.cast_succ,pow_succ]
    linarith only [h, Nat.cast_nonneg (α:=ℝ) l]

theorem front_quadratic_rank_bound {l : ℕ} (hl : 1 ≤ l) :
    (l:ℝ)*((l:ℝ)+1) ≤ 4^l/2 := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hl
  induction m with
  | zero => norm_num
  | succ m ih =>
    simp only [Nat.add_succ,Nat.cast_succ] at *
    rw [pow_succ]
    have hh : 1 ≤ ((1+m:ℕ):ℝ) := by exact_mod_cast (by omega : 1 ≤ 1+m)
    have ih' := mul_le_mul_of_nonneg_left (ih (by omega)) (by norm_num : (0:ℝ) ≤ 4)
    nlinarith only [ih',hh, sq_nonneg (((1+m:ℕ):ℝ)-1)]

/-- The old per-index coefficient estimates imply both finite tests for the
two-term error and the centered derivative. The row may be any polynomial. -/
theorem front_old_and_centered_norm (P : ℝ[X]) {h : ℕ} {a u : ℝ}
    (ha : 0 < a) (hc : P.coeff h = a) (hc' : P.coeff (h+1)=a/u)
    (hleft : ∀ j < h, |P.coeff j| * frontCoefficientWeight h (7/8*u) (9/8*u) j ≤
      (51/10*a)*(((h-j:ℕ):ℝ)+1)*(1/300)^ (h-j))
    (hright : ∀ j, h+1 < j → |P.coeff j| * frontCoefficientWeight h (7/8*u) (9/8*u) j ≤
      (9*a)*(((j-(h+1):ℕ):ℝ)+1)*(1/300)^(j-(h+1))) :
    frontCoefficientNorm (frontOldResidual P h a u) h (7/8*u) (9/8*u) < a/10 ∧
    frontCoefficientNorm (frontCenteredDerivative P h a) h (7/8*u) (9/8*u) < 3/20*a := by
  have hOld (j : ℕ) (hj : j ≠ h) (hj' : j ≠ h+1) :
      (frontOldResidual P h a u).coeff j = P.coeff j := by simp [front_old_coeff,hj,hj']
  have ho := front_norm_of_two_geometric_tails (frontOldResidual P h a u)
    (h:=h) (L:=7/8*u) (U:=9/8*u) (C₀:=51/10*a) (C₁:=9*a) (ρ:=1/150)
    (by norm_num) (by norm_num) (by positivity) (by positivity)
    (by rw [front_old_coeff,hc]; simp) (by rw [front_old_coeff,hc']; simp)
  have hd := front_norm_of_two_geometric_tails (frontCenteredDerivative P h a)
    (h:=h) (L:=7/8*u) (U:=9/8*u) (C₀:=51/10*a) (C₁:=9/2*a) (ρ:=1/75)
    (by norm_num) (by norm_num) (by positivity) (by positivity)
    (by rw [front_deriv_coeff,hc]; simp <;> ring) (by rw [front_deriv_coeff,hc']; simp)
  constructor
  · apply (ho ?_ ?_).trans_lt
    · norm_num
      linarith only [ha]
    · intro j hj
      rw [hOld j (by omega) (by omega)]
      apply (hleft j hj).trans
      rw [show (1/150:ℝ)=2*(1/300) by norm_num, mul_pow]
      convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (linear_rank_bound (h-j))
        (by positivity : 0 ≤ 51/10*a)) (by positivity : 0 ≤ (1/300:ℝ)^(h-j)) using 1 <;> ring
    · intro j hj
      rw [hOld j (by omega) (by omega)]
      apply (hright j hj).trans
      rw [show (1/150:ℝ)=2*(1/300) by norm_num, mul_pow]
      convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (linear_rank_bound (j-(h+1)))
        (by positivity : 0 ≤ 9*a)) (by positivity : 0 ≤ (1/300:ℝ)^(j-(h+1))) using 1 <;> ring
  · apply (hd ?_ ?_).trans_lt
    · norm_num
      linarith only [ha]
    · intro j hj
      have hc : (j:ℝ)-((h:ℝ)+1) = -(((h-j:ℕ):ℝ)+1) := by
        rw [Nat.cast_sub hj.le]
        ring
      rw [front_deriv_coeff, if_neg (by omega),add_zero,hc, abs_mul, abs_neg,
        abs_of_nonneg (by positivity : 0 ≤ ((h-j:ℕ):ℝ)+1),mul_assoc]
      apply (mul_le_mul_of_nonneg_left (hleft j hj) (by positivity)).trans
      rw [show (1/75:ℝ)=4*(1/300) by norm_num,mul_pow]
      have hs := pow_le_pow_left₀ (by positivity : 0 ≤ ((h-j:ℕ):ℝ)+1) (linear_rank_bound (h-j)) 2
      rw [←pow_mul, Nat.mul_comm (h-j) 2, pow_mul] at hs
      convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 51/10*a))
        (by positivity : 0 ≤ (1/300:ℝ)^(h-j)) using 1 <;> ring
    · intro j hj
      have hc : (j:ℝ)-((h:ℝ)+1) = ((j-(h+1):ℕ):ℝ) := by
        rw [Nat.cast_sub hj.le,Nat.cast_add,Nat.cast_one]
      rw [front_deriv_coeff, if_neg (by omega),add_zero,hc, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg _),mul_assoc]
      apply (mul_le_mul_of_nonneg_left (hright j hj) (by positivity)).trans
      rw [show (1/75:ℝ)=4*(1/300) by norm_num,mul_pow]
      have hs := front_quadratic_rank_bound (by omega : 1 ≤ j-(h+1))
      convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 9*a))
        (by positivity : 0 ≤ (1/300:ℝ)^(j-(h+1))) using 1 <;> ring

#print axioms front_old_and_centered_norm

#print axioms front_deriv_coeff
end OpenMathResearch.LongCycleExcedances
