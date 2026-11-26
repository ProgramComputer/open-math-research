import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic.Ring

open Finset
open scoped BigOperators

namespace OpenMathResearch.MatroidKL

/-- An integer candidate for the KL coefficient of the rank-`m` circuit. -/
def circuitKLCoeff (m j : ℕ) : ℤ :=
  if m = 0 then if j = 0 then 1 else 0
  else if j < m then
    ((m + 1).choose (j + 1) : ℤ) * ((m - j - 1).choose j : ℤ) -
      ((m + 1).choose j : ℤ) * ((m - j).choose (j + 1) : ℤ)
  else 0

theorem circuitKLCoeff_high (m j : ℕ) (hm : 0 < m) (hj : m ≤ 2 * j) : circuitKLCoeff m j = 0 := by
  unfold circuitKLCoeff
  simp only [if_neg (Nat.ne_of_gt hm)]
  split_ifs with h
  · simp [Nat.choose_eq_zero_of_lt (show m - j - 1 < j by omega),
      Nat.choose_eq_zero_of_lt (show m - j < j + 1 by omega)]
  · rfl

private theorem vandermonde_range (a b i : ℕ) :
    (∑ k ∈ Finset.range (i + 1), (a.choose k : ℤ) * (b.choose (i - k) : ℤ)) = ((a + b).choose i : ℤ) := by
  exact_mod_cast ((Nat.add_choose_eq a b i).trans
    (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun p q => a.choose p * b.choose q) i)).symm

private theorem circuitVandermonde_first (m i : ℕ) (hi : i < m) :
    (∑ k ∈ Finset.range (i + 1), ((i + 1).choose k : ℤ) * ((m - i - 1).choose (i - k) : ℤ)) =
      (m.choose i : ℤ) := by
  rw [vandermonde_range, show i + 1 + (m - i - 1) = m by omega]

private theorem circuitVandermonde_second (m i : ℕ) (hi : i < m) :
    (∑ k ∈ Finset.range (i + 1), (i.choose k : ℤ) * ((m - i).choose (i + 1 - k) : ℤ)) =
      (m.choose (i + 1) : ℤ) := by
  have h := vandermonde_range i (m - i) (i + 1)
  rw [Finset.sum_range_succ, show i + (m - i) = m by omega] at h
  simpa [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self i)] using h

private theorem circuitKLCoeff_absorption (m i k : ℕ) (hki : k ≤ i) (hi : i < m) :
    ((m + 1).choose k : ℤ) * circuitKLCoeff (m - k) (i - k) =
      ((m + 1).choose (i + 1) : ℤ) * (((i + 1).choose k : ℤ) * ((m - i - 1).choose (i - k) : ℤ)) -
      ((m + 1).choose i : ℤ) * ((i.choose k : ℤ) * ((m - i).choose (i + 1 - k) : ℤ)) := by
  have h1 : ((m + 1).choose k : ℤ) * ((m - k + 1).choose (i - k + 1) : ℤ) =
      ((m + 1).choose (i + 1) : ℤ) * ((i + 1).choose k : ℤ) := by
    have hk : k ≤ i + 1 := by omega
    have h := (Nat.choose_mul (n := m + 1) hk).symm
    rw [show m + 1 - k = m - k + 1 by omega, show i + 1 - k = i - k + 1 by omega] at h
    exact_mod_cast h
  have h2 : ((m + 1).choose k : ℤ) * ((m - k + 1).choose (i - k) : ℤ) =
      ((m + 1).choose i : ℤ) * (i.choose k : ℤ) := by
    have h := (Nat.choose_mul (n := m + 1) hki).symm
    rw [show m + 1 - k = m - k + 1 by omega] at h
    exact_mod_cast h
  unfold circuitKLCoeff
  simp only [if_neg (show m - k ≠ 0 by omega), if_pos (show i - k < m - k by omega), mul_sub]
  rw [← mul_assoc, ← mul_assoc, h1, h2]
  rw [show m - k - (i - k) = m - i by omega, show i - k + 1 = i + 1 - k by omega]
  ring

/-- The integral convolution over the proper flats gives the binomial determinant. -/
theorem circuitKLCoeff_convolution (m i : ℕ) (hi : i < m) :
    (∑ k ∈ Finset.range (i + 1), ((m + 1).choose k : ℤ) * circuitKLCoeff (m - k) (i - k)) =
      ((m + 1).choose (i + 1) : ℤ) * (m.choose i : ℤ) -
      ((m + 1).choose i : ℤ) * (m.choose (i + 1) : ℤ) := by
  calc
    _ = ∑ k ∈ Finset.range (i + 1),
        (((m + 1).choose (i + 1) : ℤ) * (((i + 1).choose k : ℤ) * ((m - i - 1).choose (i - k) : ℤ)) -
        ((m + 1).choose i : ℤ) * ((i.choose k : ℤ) * ((m - i).choose (i + 1 - k) : ℤ))) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact circuitKLCoeff_absorption m i k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hi
    _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      circuitVandermonde_first m i hi, circuitVandermonde_second m i hi]

/-- The binomial determinant is the Narayana coefficient after clearing its denominator. -/
theorem circuitNarayana_clear (m i : ℕ) (hi : i ≤ m) :
    ((m + 1 : ℕ) : ℤ) * (((m + 1).choose (i + 1) : ℤ) * (m.choose i : ℤ) -
      ((m + 1).choose i : ℤ) * (m.choose (i + 1) : ℤ)) =
      ((m + 1).choose i : ℤ) * ((m + 1).choose (i + 1) : ℤ) := by
  have cl (j : ℕ) (hj : j ≤ m + 1) : ((m.choose j : ℤ) * ((m : ℤ) + 1)) =
      ((m + 1).choose j : ℤ) * ((m : ℤ) + 1 - j) := by
    have h' : ((m.choose j : ℤ) * ((m + 1 : ℕ) : ℤ)) =
        ((m + 1).choose j : ℤ) * ((m + 1 - j : ℕ) : ℤ) := by
      exact_mod_cast Nat.choose_mul_succ_eq m j
    simpa [Nat.cast_sub hj] using h'
  push_cast
  calc
    _ = ((m + 1).choose (i + 1) : ℤ) * ((m.choose i : ℤ) * ((m : ℤ) + 1)) -
        ((m + 1).choose i : ℤ) * ((m.choose (i + 1) : ℤ) * ((m : ℤ) + 1)) := by ring
    _ = _ := by
      rw [cl i (by omega), cl (i + 1) (by omega)]
      push_cast
      ring

end OpenMathResearch.MatroidKL
