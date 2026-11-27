import StrictRootListTranslation
import Mathlib.Tactic.Ring

namespace OpenMathResearch.LongCycleExcedances
open Polynomial


theorem reflected_index_next_sign {d : ℕ} (i : Fin d) :
    (-1 : ℝ) ^ (i.rev.val + 1) = (-1 : ℝ) ^ (i.val + 1) * (-1 : ℝ) ^ (d + 1) := by
  let a : ℝ := (-1 : ℝ) ^ (i.val + 1)
  have ha : a * a = 1 := by
    dsimp only [a]
    rw [← mul_pow]
    norm_num
  have hpair : (-1 : ℝ) ^ (i.rev.val + 1) * a = (-1 : ℝ) ^ (d + 1) := by
    dsimp only [a]
    rw [← pow_add]
    congr 1
    simp only [Fin.val_rev]
    omega
  calc
    _ = (-1 : ℝ) ^ (i.rev.val + 1) * 1 := by ring
    _ = a * ((-1 : ℝ) ^ (i.rev.val + 1) * a) := by rw [← ha]; ring
    _ = _ := by rw [hpair]

theorem reciprocal_center_root_of_odd {P : ℝ[X]} {d : ℕ}
    (hrecip : ∀ t : ℝ, t ≠ 0 → t ^ d * P.eval t⁻¹ = P.eval t)
    (hodd : Odd d) :
    P.IsRoot (-1) := by
  have h := hrecip (-1) (by norm_num)
  rw [inv_neg, inv_one, hodd.neg_one_pow, neg_one_mul] at h
  change P.eval (-1) = 0
  linarith

theorem reciprocal_eval_div {P : ℝ[X]} {d : ℕ} {y : ℝ}
    (hrecip : ∀ t : ℝ, t ≠ 0 → t ^ d * P.eval t⁻¹ = P.eval t)
    (hy : 0 < y) :
    (-1 : ℝ) ^ d * P.eval (-(y⁻¹)) = P.eval (-y) / y ^ d := by
  have hr := hrecip (-y) (neg_ne_zero.mpr hy.ne')
  rw [inv_neg] at hr
  apply (eq_div_iff (pow_ne_zero _ hy.ne')).2
  calc
    _ = ((-1 : ℝ)^d * y^d) * P.eval (-(y⁻¹)) := by ring
    _ = (-y)^d * P.eval (-(y⁻¹)) := by rw [← mul_pow, neg_one_mul]
    _ = _ := hr

/-- A reciprocal polynomial transports signed values from one half-axis to
the other, with the sign changed by its degree parity. -/
theorem reciprocal_signed_pos {P : ℝ[X]} {d : ℕ} {y σ : ℝ}
    (hrecip : ∀ t : ℝ, t ≠ 0 → t ^ d * P.eval t⁻¹ = P.eval t)
    (hy : 0 < y) (hs : 0 < σ * P.eval (-y)) :
    0 < (σ * (-1 : ℝ) ^ d) * P.eval (-(y⁻¹)) := by
  rw [mul_assoc, reciprocal_eval_div hrecip hy, ← mul_div_assoc]
  exact div_pos hs (pow_pos hy _)

theorem reciprocal_root_of_root {P : ℝ[X]} {d : ℕ} {y : ℝ}
    (hrecip : ∀ t : ℝ, t ≠ 0 → t ^ d * P.eval t⁻¹ = P.eval t)
    (hy : 0 < y) (hr : P.IsRoot (-y)) :
    P.IsRoot (-(y⁻¹)) := by
  have h := reciprocal_eval_div hrecip hy
  change P.eval (-y) = 0 at hr
  rw [hr, zero_div] at h
  change P.eval (-(y⁻¹)) = 0
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (by norm_num))

theorem reciprocal_opposite_signs {P : ℝ[X]} {d : ℕ} {a b : ℝ}
    (hrecip : ∀ t : ℝ, t ≠ 0 → t ^ d * P.eval t⁻¹ = P.eval t)
    (ha : 0 < a) (hb : 0 < b) (h : P.eval (-a) * P.eval (-b) < 0) :
    P.eval (-(b⁻¹)) * P.eval (-(a⁻¹)) < 0 := by
  have ha' := reciprocal_eval_div hrecip ha
  have hb' := reciprocal_eval_div hrecip hb
  have hsq : (-1 : ℝ)^d * (-1)^d = 1 := by rw [← mul_pow]; norm_num
  calc
    _ = ((-1 : ℝ)^d * P.eval (-(a⁻¹))) *
        ((-1 : ℝ)^d * P.eval (-(b⁻¹))) := by
      calc
        _ = ((-1 : ℝ)^d * (-1)^d) * (P.eval (-(a⁻¹)) * P.eval (-(b⁻¹))) := by rw [hsq]; ring
        _ = _ := by ring
    _ = (P.eval (-a) * P.eval (-b)) / (a^d * b^d) := by
      rw [ha', hb', div_mul_div_comm]
    _ < 0 := div_neg_of_neg_of_pos h (mul_pos (pow_pos ha _) (pow_pos hb _))

#print axioms reciprocal_signed_pos
#print axioms reflected_index_next_sign
#print axioms reciprocal_center_root_of_odd
end OpenMathResearch.LongCycleExcedances
