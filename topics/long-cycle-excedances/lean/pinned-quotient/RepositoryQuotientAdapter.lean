import LongCycleBounds.GeneralCycleQuotient
import LongCycleFinite.CoefficientRows

open Polynomial Finset
open scoped BigOperators

namespace RepositoryQuotientAudit

/-- Low coefficients of the ordered support sum. An Eulerian coefficient
routine is supplied as input. The cost depends on the requested prefix. -/
def cycleFactorCoeff (e : ℕ → ℕ → ℚ) (k : ℕ) : ℕ → ℕ → ℕ → ℚ
  | 0, n, j => if n = 0 ∧ j = 0 then 1 else 0
  | h + 1, n, j =>
    ∑ a ∈ Icc k n, (n.choose a : ℚ) *
      ∑ b ∈ range (j + 1), e (a - 1) b * cycleFactorCoeff e k h (n - a) (j - b)

def cycleQuotientCoeff (e : ℕ → ℕ → ℚ) (n k j : ℕ) : ℚ :=
  ∑ h ∈ range (n / k),
    if h ≤ j then cycleFactorCoeff e k (h + 1) n (j - h) / ((h + 1).factorial : ℚ) else 0


/-- Correctness applies to any polynomial family satisfying the ordered
support recurrence, without executing arithmetic on real polynomials. -/
theorem cycleFactorCoeff_spec (e : ℕ → ℕ → ℚ) (E : ℕ → ℝ[X])
    (he : ∀ i j, (e i j : ℝ) = (E i).coeff j) (k : ℕ)
    (F : ℕ → ℕ → ℝ[X])
    (hz : ∀ n, F 0 n = if n = 0 then 1 else 0)
    (hs : ∀ h n, F (h + 1) n =
      ∑ a ∈ Icc k n, C (n.choose a : ℝ) * E (a - 1) * F h (n - a)) :
    ∀ h n j, (cycleFactorCoeff e k h n j : ℝ) = (F h n).coeff j := by
  intro h
  induction h with
  | zero =>
    intro n j
    rw [hz, cycleFactorCoeff]
    by_cases hn : n = 0 <;> by_cases hj : j = 0 <;> simp [hn, hj, coeff_one]
  | succ h ih =>
    intro n j
    rw [hs, cycleFactorCoeff]
    simp only [Polynomial.finsetSum_coeff]
    push_cast
    apply sum_congr rfl
    intro a _
    rw [mul_assoc, coeff_C_mul, coeff_mul]
    congr 1
    rw [Nat.sum_antidiagonal_eq_sum_range_succ (fun b c => (E (a - 1)).coeff b * (F h (n - a)).coeff c)]
    apply sum_congr rfl
    intro b _
    rw [he, ih]

theorem cycleQuotientCoeff_spec (e : ℕ → ℕ → ℚ) (E : ℕ → ℝ[X])
    (he : ∀ i j, (e i j : ℝ) = (E i).coeff j) (k : ℕ)
    (F : ℕ → ℕ → ℝ[X])
    (hz : ∀ n, F 0 n = if n = 0 then 1 else 0)
    (hs : ∀ h n, F (h + 1) n =
      ∑ a ∈ Icc k n, C (n.choose a : ℝ) * E (a - 1) * F h (n - a)) (n j : ℕ) :
    (cycleQuotientCoeff e n k j : ℝ) =
      (∑ h ∈ range (n / k), C (1 / ((h + 1).factorial : ℝ)) * X^h * F (h + 1) n).coeff j := by
  rw [cycleQuotientCoeff, finsetSum_coeff]
  push_cast
  apply sum_congr rfl
  intro h _
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  split_ifs with hh
  · rw [Rat.cast_div, Rat.cast_natCast, cycleFactorCoeff_spec e E he k F hz hs]
    simp [div_eq_mul_inv, mul_comm]
  · simp

open LongCycleBounds.Band LongCycles LongCycleFinite

def exactEulerianCoeff (n j : ℕ) : ℚ :=
  ((descentCoeffs n)[j]?.getD 0 : ℤ)

/-- This computes any coefficient of the quotient, including in the regime
where more than two cycles can occur. -/
theorem exact_coeff_eq_quotient (n k j : ℕ) :
    (cycleQuotientCoeff exactEulerianCoeff n k j : ℝ) = (generalCycleQuotient n k).coeff j := by
  apply cycleQuotientCoeff_spec exactEulerianCoeff eulerian _ k
    (fun h a => orderedCycleFactor a k h) _ _ n j
  · intro a b
    rw [← ofCoeffs_descentCoeffs, coeff_ofCoeffs]
    simp [exactEulerianCoeff]
  · intro a
    change orderedCycleFactor a k 0 = _
    rw [orderedCycleFactor]
  · intro a b
    change orderedCycleFactor b k (a + 1) = _
    rw [orderedCycleFactor]

/-- The output is the coefficient at exponent j+1 of the original permutation sum. -/
theorem exact_coeff_eq_original (n k j : ℕ) (hn : 0 < n) (hk : 2 ≤ k) :
    (cycleQuotientCoeff exactEulerianCoeff n k j : ℝ) = (enumerator n k).coeff (j + 1) := by
  rw [actual_general_cycle_row hk hn, coeff_X_mul, exact_coeff_eq_quotient]

end RepositoryQuotientAudit

#print axioms RepositoryQuotientAudit.exact_coeff_eq_quotient
#print axioms RepositoryQuotientAudit.exact_coeff_eq_original
