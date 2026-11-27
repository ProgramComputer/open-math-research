import TruncatedRows
import LongCycleReducedRow
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Ring

namespace OpenMathResearch.LongCycleExcedances
open Polynomial RunColors

/-- Reduction of the exact original-row insertion identity after taking out X. -/
theorem canonical_insertion_of_original {n k : ℕ} (hkn : k ≤ n) (hk : 2 ≤ k)
    (A : ℝ[X])
    (hinsertion : originalEnumerator (n + 1) k =
      C (n : ℝ) * X * originalEnumerator n k +
        X * (1 - X) * derivative (originalEnumerator n k) +
        C (n.choose (k - 1) : ℝ) * (X * A) * originalEnumerator (n + 1 - k) k) :
    canonicalReducedRow (n + 1) k =
      (1 + C ((n : ℝ) - 1) * X) * canonicalReducedRow n k +
        X * (1 - X) * derivative (canonicalReducedRow n k) +
        C (n.choose (k - 1) : ℝ) * X * A * canonicalReducedRow (n + 1 - k) k := by
  rw [original_eq_X_mul_canonical (n + 1) k (by omega) hk,
    original_eq_X_mul_canonical n k (by omega) hk,
    original_eq_X_mul_canonical (n + 1 - k) k (by omega) hk] at hinsertion
  apply mul_left_cancel₀ (X_ne_zero : (X : ℝ[X]) ≠ 0)
  rw [hinsertion, derivative_mul, derivative_X, C_sub, C_1]
  ring

theorem canonical_short_row_zero {n k : ℕ} (hn : 0 < n) (hshort : n < k) :
    canonicalReducedRow n k = 0 := by
  classical
  have hforbid (σ : Equiv.Perm (Fin n)) : ¬ cycleAllowed k σ := by
    intro hallowed
    let x : Fin n := ⟨0, hn⟩
    let f (i : Fin (n + 1)) : Fin n := (σ ^ i.val) x
    have hno (i j : Fin (n + 1)) (hl : i < j) (he : f i = f j) : False := by
      have hj : i.val + (j.val - i.val) = j.val := by omega
      have he' : (σ ^ i.val) x = (σ ^ i.val) ((σ ^ (j.val - i.val)) x) := by
        simpa only [f, ← Equiv.Perm.mul_apply, ← pow_add, hj] using he
      exact hallowed x (j.val - i.val) (by omega) (by omega)
        ((σ ^ i.val).injective he').symm
    have hf : Function.Injective f := by
      intro i j he
      rcases lt_trichotomy i j with h | h | h
      · exact (hno i j h he).elim
      · exact h
      · exact (hno j i h he.symm).elim
    simpa using Fintype.card_le_of_injective f hf
  have hz : originalEnumerator n k = 0 := by
    simp [originalEnumerator, hforbid]
  simp [canonicalReducedRow, hz]

theorem coeff_zero_of_reduced_insertion (n b : ℝ) (P Q A R : ℝ[X])
    (h : Q = (1 + C (n - 1) * X) * P + X * (1 - X) * derivative P +
      C b * X * A * R) :
    Q.coeff 0 = P.coeff 0 := by
  rw [h]
  simp [mul_coeff_zero]

/-- The one-step reduced polynomial recurrence reads only the preceding
coefficient and the local correction convolution at each positive exponent. -/
theorem coeff_of_reduced_insertion (n b : ℝ) (P Q A R : ℝ[X]) (j : ℕ)
    (h : Q = (1 + C (n - 1) * X) * P + X * (1 - X) * derivative P +
      C b * X * A * R) :
    Q.coeff (j + 1) = ((j : ℝ) + 2) * P.coeff (j + 1) +
      (n - (j + 1 : ℕ)) * P.coeff j + b * (A * R).coeff j := by
  have hs : Q = P + C (n - 1) * (X * P) +
      X * (derivative P - X * derivative P) + C b * (X * (A * R)) := by
    rw [h]
    ring
  rw [hs]
  simp only [coeff_add, coeff_C_mul, coeff_X_mul, coeff_sub, coeff_derivative]
  cases j with
  | zero =>
    simp only [coeff_X_mul_zero, Nat.cast_zero, Nat.cast_one, Nat.zero_add, sub_zero]
    ring
  | succ j =>
    rw [coeff_X_mul, coeff_derivative]
    push_cast
    ring

open Finset TruncatedRows

/-- Count the permutations contributing to a coefficient after removing X. -/
noncomputable def originalReducedCount (n k j : ℕ) : ℕ := by
  classical
  exact (univ.filter fun σ : Equiv.Perm (Fin n) => cycleAllowed k σ ∧ excedanceCount σ = j+1).card

theorem originalReducedCount_eq (n k j : ℕ) :
    (originalReducedCount n k j : ℝ) = (canonicalReducedRow n k).coeff j := by
  classical
  rw [canonicalReducedRow, coeff_divX, originalEnumerator, Polynomial.finsetSum_coeff]
  have h : ∀ σ : Equiv.Perm (Fin n), (if cycleAllowed k σ then (X : ℝ[X])^excedanceCount σ
      else 0).coeff (j+1) = if cycleAllowed k σ ∧ excedanceCount σ = j+1 then 1 else 0 := by
    intro σ
    by_cases ha : cycleAllowed k σ
    · by_cases he : excedanceCount σ = j+1
      · simp [ha, he, coeff_X_pow]
      · simp [ha, he, Ne.symm he, coeff_X_pow]
    · simp [ha]
  simp_rw [h]
  rw [← sum_filter]
  simp [originalReducedCount]

theorem originalReducedCount_above (n k j : ℕ) (hi : n < j+1) :
    originalReducedCount n k j = 0 := by
  classical
  have upper (σ : Equiv.Perm (Fin n)) : excedanceCount σ ≤ n := by
    simpa [excedanceCount] using
      (card_le_univ (univ.filter fun x : Fin n => x < σ x))
  simp only [originalReducedCount, card_eq_zero, filter_eq_empty_iff]
  intro σ _ h
  have := upper σ
  omega

theorem originalReducedCount_short (n k j : ℕ) (hn : n < k) : originalReducedCount n k j = 0 := by
  rcases n with _ | n
  · exact originalReducedCount_above 0 k j (by omega)
  · have h := originalReducedCount_eq (n+1) k j
    rw [canonical_short_row_zero (by omega) hn, coeff_zero] at h
    exact_mod_cast h

/-- The natural subtraction in the positive update agrees with signed polynomial
subtraction everywhere, including zero padding above the row's support. -/
theorem original_count_step (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n)
    (A : ℝ[X]) (a : ℕ → ℕ) (ha : ∀ j, (a j : ℝ) = A.coeff j)
    (ins : originalEnumerator (n+1) k = C (n : ℝ)*X*originalEnumerator n k +
      X*(1-X)*derivative (originalEnumerator n k) +
      C (n.choose (k-1) : ℝ)*(X*A)*originalEnumerator (n+1-k) k) (i : ℕ) :
    originalReducedCount (n+1) k i =
      positiveStep k n a (originalReducedCount n k) (originalReducedCount (n+1-k) k) i := by
  have rec := canonical_insertion_of_original hkn hk A ins
  apply Nat.cast_injective (R:=ℝ)
  rw [originalReducedCount_eq]
  cases i with
  | zero =>
    exact (coeff_zero_of_reduced_insertion _ _ _ _ _ _ rec).trans
      (originalReducedCount_eq _ _ _).symm
  | succ i =>
    rw [coeff_of_reduced_insertion _ _ _ _ _ _ i rec, coeff_mul,
      Nat.sum_antidiagonal_eq_sum_range_succ (fun j h =>
        A.coeff j * (canonicalReducedRow (n+1-k) k).coeff h)]
    simp only [positiveStep, Nat.cast_add, Nat.cast_mul, Nat.cast_sum,
      Nat.cast_ofNat, originalReducedCount_eq, ha]
    by_cases h : i+1 ≤ n
    · simp only [Nat.cast_sub h, Nat.cast_add]
    · have hz := originalReducedCount_eq n k i
      rw [originalReducedCount_above n k i (by omega : n < i+1)] at hz
      simp only [Nat.cast_zero] at hz
      rw [← hz]
      ring

/-- Once the true insertion identity and initial row are supplied, rounding
encloses the coefficients of the original permutation polynomials at every size. -/
theorem rounded_counts_within {b w k : ℕ} (hb : 0 < b) (hk : 2 ≤ k)
    (A : ℝ[X]) (a : ℕ → ℕ) (ha : ∀ j, (a j : ℝ) = A.coeff j)
    (low : ℕ → ℕ → ℕ)
    (short : ∀ n, n<k → ∀ i, i<w → low n i=0)
    (seed : ∀ i, i<w → low k i=chop b (originalReducedCount k k i))
    (ins : ∀ n, k≤n → originalEnumerator (n+1) k = C (n : ℝ)*X*originalEnumerator n k +
      X*(1-X)*derivative (originalEnumerator n k) +
      C (n.choose (k-1) : ℝ)*(X*A)*originalEnumerator (n+1-k) k)
    (step : ∀ n, k≤n → ∀ i, i<w →
      low (n+1) i=chop b (positiveStep k n a (low n) (low (n+1-k)) i))
    (n i : ℕ) (hi : i<w) :
    Within (1/2^(b-1)) n (low n i) ((canonicalReducedRow n k).coeff i) := by
  rw [← originalReducedCount_eq]
  exact all_rows_within hb (by omega : 0 < k) a (fun m => originalReducedCount m k) low
    (fun m hm j hj => ⟨originalReducedCount_short _ _ _ hm, short m hm j hj⟩) seed
    (fun m hm j hj => ⟨original_count_step _ _ hk hm A a ha (ins _ hm) _, step m hm j hj⟩)
    n i hi

#print axioms originalReducedCount_eq
#print axioms originalReducedCount_short
#print axioms original_count_step
#print axioms rounded_counts_within

end OpenMathResearch.LongCycleExcedances
