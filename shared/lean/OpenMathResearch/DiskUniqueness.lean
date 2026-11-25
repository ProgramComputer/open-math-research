import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A finite polynomial is injective in a closed complex disk when its linear
coefficient dominates the absolute derivative bound of the remaining terms. -/

namespace OpenMathResearch.DiskUniqueness

open scoped BigOperators

theorem power_difference_bound (z w : ℂ) {R : ℝ} (hz : ‖z‖ ≤ R)
    (hw : ‖w‖ ≤ R) (k : ℕ) :
    ‖z ^ (k+1) - w ^ (k+1)‖ ≤ (k+1 : ℕ) * R^k * ‖z-w‖ := by
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      ‖z ^ (k+1+1) - w ^ (k+1+1)‖ =
          ‖z * (z^(k+1) - w^(k+1)) + w^(k+1) * (z-w)‖ := by congr 1; ring
      _ ≤ ‖z‖ * ‖z^(k+1) - w^(k+1)‖ + ‖w‖^(k+1) * ‖z-w‖ := by
          simpa only [norm_mul, norm_pow] using norm_add_le
            (z * (z^(k+1) - w^(k+1))) (w^(k+1) * (z-w))
      _ ≤ R * ((k+1 : ℕ) * R^k * ‖z-w‖) + R^(k+1) * ‖z-w‖ := by
          apply add_le_add
          · exact mul_le_mul hz ih (norm_nonneg _) hR
          · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hw _) (norm_nonneg _)
      _ = _ := by push_cast; ring

/-- The term indexed by k has exponent k+1. The index set can omit zero. -/
noncomputable def evaluate (s : Finset ℕ) (a : ℕ → ℂ) (c m z : ℂ) : ℂ :=
  c + m*z + ∑ k ∈ s, a k * z^(k+1)

noncomputable def slopeBound (s : Finset ℕ) (a : ℕ → ℂ) (R : ℝ) : ℝ :=
  ∑ k ∈ s, ‖a k‖ * (k+1 : ℕ) * R^k

theorem derivative_tail_bound (s : Finset ℕ) (a : ℕ → ℂ) {R : ℝ}
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖∑ k ∈ s, a k * (k+1 : ℕ) * z^k‖ ≤ slopeBound s a R := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  simp only [norm_mul, norm_pow, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz _) (by positivity)

theorem linear_derivative_ne_zero (s : Finset ℕ) (a : ℕ → ℂ) (m : ℂ)
    {R : ℝ} (h : slopeBound s a R < ‖m‖) (z : ℂ) (hz : ‖z‖ ≤ R) :
    m + ∑ k ∈ s, a k * (k+1 : ℕ) * z^k ≠ 0 := by
  intro he
  have heq : ∑ k ∈ s, a k * (k+1 : ℕ) * z^k = -m := by linear_combination he
  have ht := derivative_tail_bound s a z hz
  rw [heq, norm_neg] at ht
  exact (not_lt_of_ge ht) h

theorem injective_on_disk (s : Finset ℕ) (a : ℕ → ℂ) (c m : ℂ) {R : ℝ}
    (h : slopeBound s a R < ‖m‖) :
    Set.InjOn (evaluate s a c m) {z : ℂ | ‖z‖ ≤ R} := by
  intro z hz w hw he
  by_contra hne
  have hdiff : 0 < ‖z-w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have heq : ∑ k ∈ s, a k * (z^(k+1) - w^(k+1)) = -(m * (z-w)) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    unfold evaluate at he
    linear_combination he
  have ht : ‖∑ k ∈ s, a k * (z^(k+1) - w^(k+1))‖ ≤ slopeBound s a R * ‖z-w‖ := by
    apply (norm_sum_le _ _).trans
    unfold slopeBound
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k _
    rw [norm_mul]
    calc
      _ ≤ ‖a k‖ * ((k+1 : ℕ) * R^k * ‖z-w‖) :=
        mul_le_mul_of_nonneg_left (power_difference_bound z w hz hw k) (norm_nonneg _)
      _ = _ := by ring
  rw [heq, norm_neg, norm_mul] at ht
  exact (not_lt_of_ge ht) (mul_lt_mul_of_pos_right h hdiff)

/-- A finite geometric comparison derived from adjacent inequalities alone. -/
theorem geometric_tail_bound (b : ℕ → ℝ) (A q : ℝ) (hq : 0 ≤ q)
    (hq1 : q < 1) (hA : b 0 ≤ A) (hA0 : 0 ≤ A)
    (step : ∀ j, b (j+1) ≤ q * b j) (n : ℕ) :
    (∑ j ∈ Finset.range n, b j) ≤ A / (1-q) := by
  have hq' : 0 < 1-q := by linarith
  have bound : ∀ j, b j ≤ q^j * A := by
    intro j
    induction j with
    | zero => simpa using hA
    | succ j ih =>
      exact (step j).trans (by simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm]
        using mul_le_mul_of_nonneg_left ih hq)
  have pointwise : ∑ j ∈ Finset.range n, b j ≤ ∑ j ∈ Finset.range n, q^j * A :=
    Finset.sum_le_sum fun j _ => bound j
  apply pointwise.trans
  apply (le_div_iff₀ hq').2
  have telescopes : ∀ m : ℕ, (∑ j ∈ Finset.range m, q^j*A)*(1-q) = A-q^m*A := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, add_mul, ih, pow_succ]; ring
  rw [telescopes]
  have := mul_nonneg (pow_nonneg hq n) hA0
  linarith

/-- The enlarged disk in the balanced-array proof has slope bound 36/37. -/
theorem extended_disk_budget (b : ℕ → ℝ) (initial : b 0 ≤ 4/5)
    (step : ∀ j, b (j+1) ≤ (8/45) * b j) (n : ℕ) :
    (∑ j ∈ Finset.range n, b j) ≤ 36/37 := by
  have h := geometric_tail_bound b (4/5) (8/45) (by norm_num) (by norm_num)
    initial (by norm_num) step n
  norm_num at h ⊢
  exact h

end OpenMathResearch.DiskUniqueness
