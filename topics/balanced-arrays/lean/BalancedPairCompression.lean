import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith

/-!
# Fixed-product compression of a complex pair

On the unit circle, a distinct pair has its sum in the interior of the segment
between the sums of the two equal pairs with the same product. An affine objective
whose squared modulus is maximal at the distinct pair has zero slope.
-/

namespace BalancedPairCompression

open Complex
open scoped ComplexConjugate

theorem unit_pair_interior {x y : ℂ} (hx : normSq x = 1) (hy : normSq y = 1)
    (hxy : x ≠ y) :
    ∃ u : ℂ, ∃ s : ℝ, normSq u = 1 ∧ u ^ 2 = x * y ∧
      -2 < s ∧ s < 2 ∧ x + y = (s : ℂ) * u := by
  by_cases hsum : x + y = 0
  · have hneg : y = -x := by
      calc
        y = (x + y) - x := by ring
        _ = -x := by simp [hsum]
    refine ⟨x * I, 0, by simp [normSq_mul, hx], ?_, by norm_num, by norm_num, ?_⟩
    · rw [mul_pow, I_sq, hneg]
      ring
    · simpa using hsum
  · let s := Real.sqrt (normSq (x + y))
    have hs_pos : 0 < s := Real.sqrt_pos.2 (normSq_pos.2 hsum)
    have hs_mul : s * s = normSq (x + y) := Real.mul_self_sqrt (normSq_nonneg _)
    have hcz : (s : ℂ) ≠ 0 := ofReal_ne_zero.2 hs_pos.ne'
    have hpar : normSq (x + y) + normSq (x - y) = 4 := by
      rw [normSq_add, normSq_sub, hx, hy]
      ring
    have hdiff : 0 < normSq (x - y) := normSq_pos.2 (sub_ne_zero.2 hxy)
    let u := (x + y) / (s : ℂ)
    have hu : normSq u = 1 := by
      dsimp [u]
      rw [normSq_div, normSq_ofReal, hs_mul, div_self (normSq_pos.2 hsum).ne']
    have hxc : conj x * x = 1 := by
      rw [← normSq_eq_conj_mul_self, hx, ofReal_one]
    have hyc : conj y * y = 1 := by
      rw [← normSq_eq_conj_mul_self, hy, ofReal_one]
    have hproduct : (conj x + conj y) * (x * y) = x + y := by
      calc
        (conj x + conj y) * (x * y) = (conj x * x) * y + (conj y * y) * x := by ring
        _ = x + y := by rw [hxc, hyc, one_mul, one_mul, add_comm]
    have hu_sq : u ^ 2 = x * y := by
      dsimp [u]
      rw [div_pow]
      apply (div_eq_iff (pow_ne_zero _ hcz)).2
      rw [pow_two (s : ℂ), ← ofReal_mul, hs_mul, normSq_eq_conj_mul_self, map_add]
      calc
        (x + y) ^ 2 = (x + y) * ((conj x + conj y) * (x * y)) := by
          rw [hproduct, pow_two]
        _ = x * y * ((conj x + conj y) * (x + y)) := by ring
    refine ⟨u, s, hu, hu_sq, by linarith, ?_, ?_⟩
    · nlinarith
    · dsimp [u]
      rw [mul_comm, div_mul_cancel₀ _ hcz]

private theorem affine_normSq_identity (a b : ℂ) (s : ℝ) :
    normSq (a + (s : ℂ) * b) + (4 - s ^ 2) * normSq b =
      ((2 + s) / 4) * normSq (a + ((2 : ℝ) : ℂ) * b) +
      ((2 - s) / 4) * normSq (a - ((2 : ℝ) : ℂ) * b) := by
  simp only [normSq_apply, add_re, add_im, sub_re, sub_im, mul_re, mul_im, ofReal_re,
    ofReal_im]
  ring

/-- A strict interior point of a nonconstant complex affine segment has smaller squared
norm than at least one of its endpoints. -/
theorem affine_normSq_lt_endpoint (a b : ℂ) (s : ℝ) (hb : b ≠ 0)
    (hlo : -2 < s) (hhi : s < 2) :
    normSq (a + (s : ℂ) * b) < normSq (a + ((2 : ℝ) : ℂ) * b) ∨
    normSq (a + (s : ℂ) * b) < normSq (a - ((2 : ℝ) : ℂ) * b) := by
  by_contra! h
  have hplus := mul_le_mul_of_nonneg_left h.1 (show 0 ≤ (2 + s) / 4 by linarith)
  have hminus := mul_le_mul_of_nonneg_left h.2 (show 0 ≤ (2 - s) / 4 by linarith)
  have hs : 0 < 4 - s ^ 2 := by
    have hproduct := mul_pos (show 0 < 2 + s by linarith) (show 0 < 2 - s by linarith)
    nlinarith only [hproduct]
  have hgap := mul_pos hs (normSq_pos.2 hb)
  linarith only [affine_normSq_identity a b s, hplus, hminus, hgap]

/-- A distinct unit pair has an equal-pair replacement with the same product and
strictly larger squared modulus of any affine objective with nonzero slope. -/
theorem exists_compressing_unit_pair {x y : ℂ} (hx : normSq x = 1) (hy : normSq y = 1)
    (hxy : x ≠ y) (a b : ℂ) (hb : b ≠ 0) :
    ∃ u : ℂ, normSq u = 1 ∧ u ^ 2 = x * y ∧
      normSq (a + b * (x + y)) < normSq (a + b * (u + u)) := by
  obtain ⟨u, s, hu, hprod, hlo, hhi, hsum⟩ := unit_pair_interior hx hy hxy
  have hbu : b * u ≠ 0 := mul_ne_zero hb (normSq_pos.1 (by rw [hu]; norm_num))
  have hcurrent : a + (s : ℂ) * (b * u) = a + b * (x + y) := by rw [hsum]; ring
  rcases affine_normSq_lt_endpoint a (b * u) s hbu hlo hhi with h | h
  · refine ⟨u, hu, hprod, ?_⟩
    have heq : a + ((2 : ℝ) : ℂ) * (b * u) = a + b * (u + u) := by
      norm_cast
      ring
    simpa only [hcurrent, heq] using h
  · refine ⟨-u, by simpa using hu, by simpa using hprod, ?_⟩
    have heq : a - ((2 : ℝ) : ℂ) * (b * u) = a + b * (-u + -u) := by
      norm_cast
      ring
    simpa only [hcurrent, heq] using h

/-- At a distinct maximal pair, a symmetric affine objective has zero slope. -/
theorem slope_eq_zero_at_unit_pair_max {x y : ℂ} (hx : normSq x = 1) (hy : normSq y = 1)
    (hxy : x ≠ y) (a b : ℂ)
    (hmax : ∀ u : ℂ, normSq u = 1 → u ^ 2 = x * y →
      normSq (a + b * (u + u)) ≤ normSq (a + b * (x + y))) : b = 0 := by
  by_contra hb
  obtain ⟨u, hu, hp, hlt⟩ := exists_compressing_unit_pair hx hy hxy a b hb
  exact (not_le_of_gt hlt) (hmax u hu hp)

end BalancedPairCompression
