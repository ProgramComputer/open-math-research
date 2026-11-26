import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OpenMathResearch.FiniteTailMoments

open Finset
open scoped BigOperators

noncomputable section

def tail (p : ℕ → ℝ) (r a : ℕ) : ℝ :=
  ∑ j ∈ range (r + 1), p (a + j)

theorem tail_eq_zero {p : ℕ → ℝ} {r a : ℕ} (hp : ∀ i > r, p i = 0) (ha : r < a) :
    tail p r a = 0 := by
  unfold tail
  exact Finset.sum_eq_zero fun j _ => hp _ (by omega)

theorem tail_step {p : ℕ → ℝ} {r : ℕ} (hp : ∀ i > r, p i = 0) (a : ℕ) :
    tail p r a = p a + tail p r (a + 1) := by
  unfold tail
  conv_lhs => rw [Finset.sum_range_succ']
  conv_rhs => rw [Finset.sum_range_succ]
  simp only [Nat.add_zero, hp (a + 1 + r) (by omega), add_zero]
  rw [add_comm (p a)]
  apply congrArg (fun x : ℝ => x + p a)
  exact Finset.sum_congr rfl fun j _ => by congr 1; omega

theorem tail_split {p : ℕ → ℝ} {r : ℕ} (hp : ∀ i > r, p i = 0) (a b : ℕ) :
    tail p r a = (∑ j ∈ range b, p (a + j)) + tail p r (a + b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, ih, tail_step hp (a+b)]
    rw [show a + (b + 1) = a + b + 1 by omega]
    ring

/-- A decreasing shifted likelihood ratio yields submultiplicative
survival probabilities by comparing every low index with every high index. -/
theorem tail_submultiplicative {p : ℕ → ℝ} {r : ℕ} (hp : ∀ i > r, p i = 0)
    (h1 : tail p r 0 = 1)
    (hcross : ∀ a i j : ℕ, i ≤ j → p (a + j) * p i ≤ p (a + i) * p j)
    (a b : ℕ) :
    tail p r (a + b) ≤ tail p r a * tail p r b := by
  have hlow : tail p r (a+b) * (∑ i ∈ range b, p i) ≤
      (∑ i ∈ range b, p (a+i)) * tail p r b := by
    rw [mul_comm (tail p r (a+b)), tail, tail, Finset.sum_mul_sum, Finset.sum_mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j _
    rw [mul_comm (p i), Nat.add_assoc]
    exact hcross a i (b+j) (by have := Finset.mem_range.mp hi; omega)
  have htotal := tail_split hp 0 b
  simp only [Nat.zero_add, h1] at htotal
  rw [tail_split hp a b]
  nlinarith only [hlow, congrArg (fun x : ℝ => tail p r (a+b) * x) htotal]

/-- Summation by parts for the finite tail, including the zero beyond the cap. -/
theorem sum_weighted_tail {p : ℕ → ℝ} {r : ℕ} (hp : ∀ i > r, p i = 0)
    (f : ℕ → ℝ) :
    ∑ j ∈ range (r + 1), p j * f j =
      tail p r 0 * f 0 + ∑ j ∈ range (r + 1), tail p r (j+1) * (f (j+1) - f j) := by
  calc
    _ = (∑ j ∈ range (r+1), (tail p r j * f j - tail p r (j+1) * f (j+1))) +
      ∑ j ∈ range (r+1), tail p r (j+1) * (f (j+1) - f j) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        have h := tail_step hp j
        rw [h]
        ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_range_succ' (fun j => tail p r j * f j),
        Finset.sum_range_succ (fun j => tail p r (j+1) * f (j+1)),
        tail_eq_zero hp (Nat.lt_succ_self r)]
      ring

theorem mean_eq_sum_tail {p : ℕ → ℝ} {r : ℕ} (hp : ∀ i > r, p i = 0) :
    ∑ j ∈ range (r+1), p j * (j : ℝ) =
      ∑ j ∈ range (r+1), tail p r (j+1) := by
  rw [sum_weighted_tail hp]
  simp

theorem factorialHalf_le_mean_sq {p : ℕ → ℝ} {r : ℕ}
    (hp : ∀ i > r, p i = 0) (h1 : tail p r 0 = 1)
    (hcross : ∀ a i j : ℕ, i ≤ j → p (a + j) * p i ≤ p (a + i) * p j) :
    (∑ j ∈ range (r+1), p j * ((j : ℝ) * ((j : ℝ)-1) / 2)) ≤
      (∑ j ∈ range (r+1), p j * (j : ℝ)) ^ 2 := by
  let q := fun j => tail p r (j+1)
  have hq : ∀ i > r, q i = 0 := fun i hi => tail_eq_zero hp (by omega)
  have hf : (∑ j ∈ range (r+1), p j * ((j : ℝ) * ((j : ℝ)-1) / 2)) =
      ∑ j ∈ range (r+1), q j * (j : ℝ) := by
    rw [sum_weighted_tail hp]
    simp only [Nat.cast_zero, zero_mul, zero_div, mul_zero, zero_add]
    apply Finset.sum_congr rfl
    intro j _
    simp only [q, Nat.cast_add, Nat.cast_one]
    ring
  rw [hf, mean_eq_sum_tail hq, mean_eq_sum_tail hp]
  simp only [pow_two, tail, q]
  -- Fold all inner sums back into tails of p.
  change (∑ i ∈ range (r+1), ∑ j ∈ range (r+1), tail p r ((i+1+j)+1)) ≤
    (∑ i ∈ range (r+1), tail p r (i+1)) * (∑ j ∈ range (r+1), tail p r (j+1))
  rw [Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  rw [Nat.add_assoc]
  exact tail_submultiplicative hp h1 hcross (i+1) (j+1)

theorem variance_le_mean_one_add_mean {p : ℕ → ℝ} {r : ℕ}
    (hp : ∀ i > r, p i = 0) (h1 : tail p r 0 = 1)
    (hcross : ∀ a i j : ℕ, i ≤ j → p (a+j) * p i ≤ p (a+i) * p j) :
    let m := ∑ j ∈ range (r+1), p j * (j : ℝ)
    (∑ j ∈ range (r+1), p j * ((j : ℝ)-m)^2) ≤ m * (1 + m) := by
  let m := ∑ j ∈ range (r+1), p j * (j : ℝ)
  have hmass : (∑ j ∈ range (r+1), p j) = 1 := by simpa [tail] using h1
  have hf := factorialHalf_le_mean_sq hp h1 hcross
  change _ ≤ m * (1+m)
  have heq : (∑ j ∈ range (r+1), p j * ((j : ℝ)-m)^2) =
      2 * (∑ j ∈ range (r+1), p j * ((j : ℝ) * ((j : ℝ)-1) / 2)) + m - m^2 := by
    calc
      _ = ∑ j ∈ range (r+1), (2 * (p j * ((j : ℝ) * ((j : ℝ)-1) / 2)) +
          p j * (j : ℝ) - (p j * (j : ℝ)) * (2*m) + p j * m^2) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul, hmass]
        change _ + m - m * (2*m) + 1*m^2 = _
        ring
  rw [heq]
  change _ ≤ m * (1+m)
  change _ ≤ m ^ 2 at hf
  linarith

#print axioms tail_submultiplicative
#print axioms variance_le_mean_one_add_mean

end

end OpenMathResearch.FiniteTailMoments
