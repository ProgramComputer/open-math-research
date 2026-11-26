import CatalanStrictPeaksFirstReturn
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Bounds

/-!
# A checker for packed strict Catalan peak coefficients

The certified first-return decomposition gives a scalar convolution for
the polynomial values at a fixed integer. Checking these identities for
a candidate prefix certifies its values, and sufficiently large-base
digits recover the coefficients of every row.
-/

namespace CatalanStrictPeaks.FastCoefficients

open Finset Polynomial

private noncomputable def convolution (n : ℕ) : ℝ[X] :=
  ∑ i ∈ range (n + 1), C i * C (n - i)

private theorem row_zero : C 0 = 1 := (Recurrence.enumerate_X_eq_C 0).symm

private theorem row_one : C 1 = convolution 0 := by
  simp [FirstReturn.C_succ_split, convolution]

private theorem row_add_two (n : ℕ) :
    C (n + 2) = convolution (n + 1) + (X - 1) * (convolution n - C n) := by
  rw [FirstReturn.C_succ_split, sum_add_distrib]
  change convolution (n + 1) + _ = _
  congr 1
  simp_rw [mul_assoc, ← mul_sum]
  congr 1
  rw [sum_range_succ']
  simp only [FirstReturn.A_zero, zero_mul, add_zero, FirstReturn.A_succ,
    Nat.succ_lt_succ_iff, Nat.succ_sub_succ_eq_sub]
  have hconv : convolution n - C n = ∑ i ∈ range n, C i * C (n - i) := by
    rw [convolution, sum_range_succ, Nat.sub_self, row_zero, mul_one, add_sub_cancel_right]
  rw [hconv, sum_range_succ]
  simp only [lt_self_iff_false, if_false, mul_zero, add_zero]
  exact sum_congr rfl fun i hi => by simp [mem_range.mp hi]

private theorem eval_one_eq_catalan (n : ℕ) : (C n).eval 1 = (catalan n : ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [row_zero]
    | succ n =>
      rw [FirstReturn.C_succ_split, catalan_succ',
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => catalan i * catalan j) n,
        eval_finset_sum, Nat.cast_sum]
      apply sum_congr rfl
      intro i hi
      have hi' := mem_range.mp hi
      simp only [eval_add, eval_mul, eval_sub, eval_X, Polynomial.eval_one, sub_self, zero_mul, add_zero,
        Nat.cast_mul]
      rw [ih i (by omega), ih (n - i) (by omega)]

private theorem word_count (n : ℕ) : (words n).card = catalan n := by
  have h : (C n).eval 1 = ((words n).card : ℝ) := by simp [C, eval_finset_sum, eval_pow]
  exact_mod_cast h.symm.trans (eval_one_eq_catalan n)

/-- A common base exceeding the word counts of the prefix. -/
def base (last : ℕ) : ℕ := 4 ^ last + 1

private theorem word_count_lt_base {n last : ℕ} (hn : n ≤ last) :
    (words n).card < base last := by
  rw [word_count, catalan_eq_centralBinom_div, base, Nat.lt_succ_iff]
  refine (Nat.div_le_self _ _).trans ?_
  have hbinom : n.centralBinom ≤ 4 ^ n := by
    cases n with
    | zero => decide
    | succ n =>
      rw [Nat.centralBinom, show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul]
      exact (Nat.choose_le_two_pow _ _ (by omega)).le
  exact hbinom.trans (Nat.pow_le_pow_right (by decide) hn)

/-- One candidate evaluation at the coefficient base per row. -/
abbrev Values := Array ℕ

def entry (values : Values) (i : ℕ) : ℕ := values.toList[i]?.getD 0

private def convolve (values : Values) (n : ℕ) : ℕ :=
  ((List.range (n + 1)).map (fun i => entry values i * entry values (n - i))).sum

/-- Check the recurrence using the certificate entries preceding `n + 1`.
Move the subtraction across the equality to use natural-number arithmetic. -/
def checkStep (q : ℕ) (values : Values) (n : ℕ) : Bool :=
  match n with
  | 0 => decide (entry values 1 = convolve values 0)
  | k + 1 => decide (entry values (k + 2) + (q - 1) * entry values k =
      convolve values (k + 1) + (q - 1) * convolve values k)

private theorem sum_list_range {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, sum_range_succ, ih]

private theorem convolve_correct {q : ℕ} {prior : Values} {n : ℕ}
    (h : ∀ i ≤ n, (entry prior i : ℝ) = (C i).eval (q : ℝ)) :
    (convolve prior n : ℝ) = (convolution n).eval (q : ℝ) := by
  rw [convolve, sum_list_range, convolution, Nat.cast_sum, eval_finset_sum]
  apply sum_congr rfl
  intro i hi
  rw [Nat.cast_mul, eval_mul, h i (by have := mem_range.mp hi; omega), h (n - i) (Nat.sub_le ..)]

private theorem values_correct {q : ℕ} {values : Values} {last : ℕ} (hq : 1 ≤ q)
    (hzero : entry values 0 = 1) (hsteps : ∀ n < last, checkStep q values n = true) :
    ∀ n ≤ last, (entry values n : ℝ) = (C n).eval (q : ℝ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => simp [hzero, row_zero]
    | succ n =>
      have hs := hsteps n (by omega)
      cases n with
      | zero =>
        have hstep : entry values 1 = convolve values 0 := of_decide_eq_true hs
        rw [hstep, convolve_correct (fun i hi => ih i (by omega) (by omega)), row_one]
      | succ n =>
        have hstep : entry values (n + 2) + (q - 1) * entry values n =
            convolve values (n + 1) + (q - 1) * convolve values n := of_decide_eq_true hs
        have hcast := congrArg (fun x : ℕ => (x : ℝ)) hstep
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hq, Nat.cast_one] at hcast
        rw [convolve_correct (fun i hi => ih i (by omega) (by omega)),
          convolve_correct (fun i hi => ih i (by omega) (by omega)),
          ih n (by omega) (by omega)] at hcast
        change (entry values (n + 2) : ℝ) = _
        rw [row_add_two]
        simp only [eval_add, eval_mul, eval_sub, eval_X, eval_one]
        rw [mul_sub, ← add_sub_assoc, ← hcast, add_sub_cancel_right]

private theorem cast_enumerate (q n : ℕ) :
    ((Recurrence.enumerate q n : ℕ) : ℝ) = (C n).eval (q : ℝ) := by
  simp [Recurrence.enumerate_eq_sum_words, C, eval_finset_sum, eval_pow, Nat.cast_sum, Nat.cast_pow]

/-- Recover the coefficients of row `n` from the stored prefix table. -/
def row (last n : ℕ) (computed : Values) : List ℕ :=
  let b := base last
  let value := entry computed n
  List.ofFn (fun k : Fin (rowDegree n + 1) => value / b ^ k.val % b)

/-- A checked prefix of packed evaluations gives the original coefficients. -/
theorem row_eq_coefficients {last n : ℕ} {computed : Values}
    (hzero : entry computed 0 = 1)
    (hsteps : ∀ i < last, checkStep (base last) computed i = true) (hn : n ≤ last) :
    row last n computed = Recurrence.coefficients n := by
  have hq : 1 ≤ base last := by simp [base]
  have h := values_correct hq hzero hsteps n hn
  rw [← cast_enumerate] at h
  have h' : entry computed n = Recurrence.enumerate (base last) n := by exact_mod_cast h
  simp only [row, h']
  exact Recurrence.digits_eq_coefficients _ _ (word_count_lt_base hn)

end CatalanStrictPeaks.FastCoefficients
