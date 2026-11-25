import PrismSeriesClosure
import Mathlib.RingTheory.Binomial

/-!
The signed binomial form of the lattice counts for the infinite family.
-/

namespace PrismFamily

open PrismSplit
open scoped BigOperators fwdDiff

def beforeCaps (b : Nat) : List Nat := List.replicate (2 * b) 1 ++ [2]

def afterCaps (b : Nat) : List Nat := List.replicate (2 * b + 2) 1

def beforeCounts (b q : Nat) : Int :=
  (integerPointCount (beforeCaps b) (b + 1) q : Int)

def afterCounts (b q : Nat) : Int :=
  (integerPointCount (afterCaps b) (b + 1) q : Int)

theorem beforeCounts_eq (b : Nat) (hb : 2 ≤ b) :
    beforeCounts b =
      signedRows (2 * b) (2 * b) (b + 1) 0 0 - signedRows (2 * b) (2 * b) (b + 1) 2 1 := by
  funext q
  simp only [beforeCounts, integerPointCount, cardinality_eq_boundedCount, beforeCaps, dilatedCaps,
    List.map_append, List.map_replicate, mul_one, List.map_cons, List.map_nil]
  rw [mul_comm q 2, mul_comm q (b + 1), ← boxSeries_coeff, boxSeries_append, boxSeries_replicate]
  simp only [boxSeries, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [capSeries_eq, capSeries_eq, mul_pow]
  have h :
      (1 - PowerSeries.X ^ (q + 1)) ^ (2 * b) * (PowerSeries.mk 1 : PowerSeries Int) ^ (2 * b) *
        ((1 - PowerSeries.X ^ (2 * q + 1)) * PowerSeries.mk 1) =
      (1 - PowerSeries.X ^ (q + 1)) ^ (2 * b) * PowerSeries.X ^ (0 * q + 0) *
        (PowerSeries.mk 1 : PowerSeries Int) ^ (2 * b + 1) -
      (1 - PowerSeries.X ^ (q + 1)) ^ (2 * b) * PowerSeries.X ^ (2 * q + 1) *
        (PowerSeries.mk 1 : PowerSeries Int) ^ (2 * b + 1) := by
    simp only [zero_mul, zero_add, pow_zero, mul_one, pow_succ (PowerSeries.mk 1) (2 * b)]
    ring
  rw [h, PowerSeries.mk_one_pow_eq_mk_choose_add, map_sub,
    coeff_signedRows q _ _ _ 0 0 (by omega) (by omega),
    coeff_signedRows q _ _ _ 2 1 (by omega) (by omega)]
  rfl

theorem afterCounts_eq (b : Nat) :
    afterCounts b = signedRows (2 * b + 2) (2 * b + 1) (b + 1) 0 0 := by
  funext q
  simp only [afterCounts, integerPointCount, cardinality_eq_boundedCount, afterCaps, dilatedCaps,
    List.map_replicate, mul_one]
  rw [mul_comm q (b + 1), ← boxSeries_coeff, boxSeries_replicate, capSeries_eq, mul_pow,
    PowerSeries.mk_one_pow_eq_mk_choose_add Int (2 * b + 1)]
  have h := coeff_signedRows q (2 * b + 2) (2 * b + 1) (b + 1) 0 0 (by omega) (by omega)
  simpa only [zero_mul, zero_add, pow_zero, mul_one] using h

def intAffineChoose (s u d : Nat) : Int → Int :=
  fun q => Ring.choose ((s : Int) * q + (u : Int)) d

private theorem intAffineChoose_nat (s u d q : Nat) :
    intAffineChoose s u d (q : Int) = affineChoose s u d q := by
  rw [intAffineChoose, ← Nat.cast_mul, ← Nat.cast_add, Ring.choose_natCast]
  rfl

noncomputable def intSignedRows (n d k w e : Nat) : Int → Int :=
  ∑ j ∈ Finset.range (n + 1),
    if j + w < k then
      ((-1 : Int) ^ j * (n.choose j : Int)) • intAffineChoose (k - (j + w)) (d - (j + e)) d
    else 0

theorem intSignedRows_nat (n d k w e q : Nat) :
    intSignedRows n d k w e (q : Int) = signedRows n d k w e q := by
  rw [intSignedRows, signedRows, Finset.sum_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j + w < k <;>
    simp only [hj, if_true, if_false, Pi.smul_apply, Pi.zero_apply, intAffineChoose_nat]

private theorem int_choose_difference (x : Int) (a d : Nat) :
    Ring.choose (x + (a : Int)) (d + 1) - Ring.choose x (d + 1) =
      ∑ i ∈ Finset.range a, Ring.choose (x + (i : Int)) d := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.cast_succ, ← add_assoc, Ring.choose_succ_succ, Finset.sum_range_succ, ← ih]
    ring

private theorem intAffineChoose_difference (a b d : Nat) :
    Δ_[1] (intAffineChoose a b (d + 1)) =
      ∑ i ∈ Finset.range a, intAffineChoose a (b + i) d := by
  funext q
  rw [fwdDiff, Finset.sum_apply, intAffineChoose, intAffineChoose]
  simp only [mul_add, mul_one]
  rw [show (a : Int) * q + (a : Int) + (b : Int) =
    ((a : Int) * q + (b : Int)) + (a : Int) by abel, int_choose_difference]
  simp only [intAffineChoose, Nat.cast_add, add_assoc]

private theorem intAffineChoose_difference_zero (a b d : Nat) :
    Δ_[1]^[d + 1] (intAffineChoose a b d) = 0 := by
  induction d generalizing a b with
  | zero =>
    have h : intAffineChoose a b 0 = fun _ => 1 := by
      funext q
      simp [intAffineChoose, Ring.choose_zero_right]
    rw [h, Function.iterate_one, fwdDiff_const]
    rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply, intAffineChoose_difference, fwdDiff_iter_finset_sum]
    simp [ih]

theorem intSignedRows_difference_zero (n d k w e : Nat) :
    Δ_[1]^[d + 1] (intSignedRows n d k w e) = 0 := by
  rw [intSignedRows, fwdDiff_iter_finset_sum]
  apply Finset.sum_eq_zero
  intro j _
  split
  · rw [fwdDiff_iter_const_smul, intAffineChoose_difference_zero, smul_zero]
  · exact Function.iterate_fixed (fwdDiff_const (M := Int) (h := 1) (0 : Int)) (d + 1)

noncomputable def beforeIntExtension (b : Nat) : Int → Int :=
  intSignedRows (2 * b) (2 * b) (b + 1) 0 0 - intSignedRows (2 * b) (2 * b) (b + 1) 2 1

noncomputable def afterIntExtension (b : Nat) : Int → Int :=
  intSignedRows (2 * b + 2) (2 * b + 1) (b + 1) 0 0

theorem beforeIntExtension_nat (b q : Nat) (hb : 2 ≤ b) :
    beforeIntExtension b (q : Int) = beforeCounts b q := by
  rw [beforeCounts_eq b hb, beforeIntExtension, Pi.sub_apply, Pi.sub_apply,
    intSignedRows_nat, intSignedRows_nat]

theorem afterIntExtension_nat (b q : Nat) :
    afterIntExtension b (q : Int) = afterCounts b q := by
  rw [afterCounts_eq, afterIntExtension, intSignedRows_nat]

theorem beforeIntExtension_diff (b : Nat) :
    Δ_[1]^[(2 * b) + 1] (beforeIntExtension b) = 0 := by
  rw [beforeIntExtension, sub_eq_add_neg, ← neg_one_smul ℤ, fwdDiff_iter_add,
    fwdDiff_iter_const_smul, intSignedRows_difference_zero, intSignedRows_difference_zero]
  simp

theorem afterIntExtension_diff (b : Nat) :
    Δ_[1]^[(2 * b + 1) + 1] (afterIntExtension b) = 0 :=
  intSignedRows_difference_zero _ _ _ _ _

private theorem beforeCounts_diff (b : Nat) (hb : 2 ≤ b) :
    Δ_[1]^[(2 * b) + 1] (beforeCounts b) = 0 := by
  rw [beforeCounts_eq b hb, sub_eq_add_neg, ← neg_one_smul ℤ, fwdDiff_iter_add,
    fwdDiff_iter_const_smul, signedRows_difference_zero, signedRows_difference_zero]
  simp

private theorem afterCounts_diff (b : Nat) :
    Δ_[1]^[(2 * b + 1) + 1] (afterCounts b) = 0 := by
  rw [afterCounts_eq]
  exact signedRows_difference_zero _ _ _ _ _

noncomputable def beforeNumerator (b : Nat) : Polynomial Int :=
  polynomialPrefix (2 * b) (normalizedCountSeries (2 * b) (beforeCounts b))

noncomputable def afterNumerator (b : Nat) : Polynomial Int :=
  polynomialPrefix (2 * b + 1) (normalizedCountSeries (2 * b + 1) (afterCounts b))

theorem beforeNumeratorSeries (b : Nat) (hb : 2 ≤ b) :
    (beforeNumerator b : PowerSeries Int) = normalizedCountSeries (2 * b) (beforeCounts b) :=
  polynomialPrefix_series _ _ (normalized_zero_above _ _ (beforeCounts_diff b hb))

theorem afterNumeratorSeries (b : Nat) :
    (afterNumerator b : PowerSeries Int) = normalizedCountSeries (2 * b + 1) (afterCounts b) :=
  polynomialPrefix_series _ _ (normalized_zero_above _ _ (afterCounts_diff b))

#print axioms beforeIntExtension_nat
#print axioms afterIntExtension_nat
#print axioms beforeIntExtension_diff
#print axioms afterIntExtension_diff
#print axioms beforeNumeratorSeries
#print axioms afterNumeratorSeries

end PrismFamily
