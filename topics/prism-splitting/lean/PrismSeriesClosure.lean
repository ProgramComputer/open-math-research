import PrismGeometry
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
Concrete polynomiality of the Ehrhart count series in the prism split.
The proof operates on the bounded-composition generating series and finite
differences, without a general lattice-polytope Ehrhart theorem.
-/

namespace PrismSplit

open scoped BigOperators fwdDiff

private noncomputable def capSeries (c : Nat) : PowerSeries Int :=
  ∑ j ∈ Finset.range (c + 1), PowerSeries.X ^ j

private noncomputable def boxSeries (caps : List Nat) : PowerSeries Int :=
  (caps.map capSeries).prod

private theorem sum_range_eq_list (f : Nat → Int) (m : Nat) :
    (∑ j ∈ Finset.range m, f j) = ((List.range m).map f).sum := by
  induction m with
  | zero => simp
  | succ m ih => simp [Finset.sum_range_succ, ih, List.range_succ, List.sum_append]

private theorem boxSeries_coeff (caps : List Nat) (t : Nat) :
    PowerSeries.coeff Int t (boxSeries caps) = (boundedCount caps t : Int) := by
  rw [boundedCount_eq_length]
  induction caps generalizing t with
  | nil =>
    by_cases ht : t = 0 <;> simp [boxSeries, boundedCompositions, PowerSeries.coeff_one, ht]
  | cons c caps ih =>
    change PowerSeries.coeff Int t (capSeries c * boxSeries caps) =
      ((boundedCompositions (c :: caps) t).length : Int)
    rw [capSeries, Finset.sum_mul, map_sum]
    simp only [PowerSeries.coeff_X_pow_mul', ih]
    rw [← Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (min_le_left c t)))]
    · rw [boundedCompositions, List.length_flatMap, sum_range_eq_list]
      simp only [List.length_map]
      push_cast
      rw [List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro j hj
      rw [if_pos ((Nat.le_of_lt_succ (List.mem_range.mp hj)).trans (min_le_right c t))]
      rfl
    · intro j hj hj'
      apply if_neg
      intro hjt
      apply hj'
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le
        (le_min (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hjt))

private theorem capSeries_mul_one_sub (c : Nat) :
    capSeries c * (1 - PowerSeries.X) = 1 - PowerSeries.X ^ (c + 1) := by
  induction c with
  | zero => simp [capSeries]
  | succ c ih =>
    unfold capSeries at *
    rw [Finset.sum_range_succ, add_mul, ih]
    simp only [mul_sub, mul_one, ← pow_succ]
    ring

private theorem capSeries_eq (c : Nat) :
    capSeries c = (1 - PowerSeries.X ^ (c + 1)) * (PowerSeries.mk 1 : PowerSeries Int) := by
  calc
    capSeries c = capSeries c * ((1 - PowerSeries.X) * PowerSeries.mk 1) := by
      rw [mul_comm (1 - PowerSeries.X), PowerSeries.mk_one_mul_one_sub_eq_one, mul_one]
    _ = _ := by
      rw [← mul_assoc, capSeries_mul_one_sub]

private theorem boxSeries_replicate (c n : Nat) :
    boxSeries (List.replicate n c) = capSeries c ^ n := by
  simp [boxSeries, List.map_replicate, List.prod_replicate]

private theorem boxSeries_append (a b : List Nat) :
    boxSeries (a ++ b) = boxSeries a * boxSeries b := by
  simp [boxSeries]

private theorem one_sub_X_pow_expansion (p n : Nat) :
    (1 - PowerSeries.X ^ p : PowerSeries Int) ^ n =
      ∑ j ∈ Finset.range (n + 1),
        PowerSeries.C Int ((-1 : Int) ^ j * (n.choose j : Int)) * PowerSeries.X ^ (p * j) := by
  rw [sub_eq_add_neg, add_comm, add_pow]
  apply Finset.sum_congr rfl
  intro j _
  have hneg : -(PowerSeries.X ^ p : PowerSeries Int) =
      PowerSeries.C Int (-1) * PowerSeries.X ^ p := by simp
  rw [hneg, one_pow, mul_one, mul_pow, ← pow_mul]
  simp only [map_mul, map_pow, map_natCast]
  ring

private def affineChoose (s b d : Nat) : Nat → Int :=
  fun q => ((s * q + b).choose d : Int)

private noncomputable def signedRows (n d w e : Nat) : Nat → Int :=
  ∑ j ∈ Finset.range (n + 1),
    if j + w < 6 then
      ((-1 : Int) ^ j * (n.choose j : Int)) • affineChoose (6 - (j + w)) (d - (j + e)) d
    else 0

private theorem coeff_shifted_choose (q j w e d : Nat) (hw : w ≤ 5) (hd : 5 + e ≤ d) :
    PowerSeries.coeff Int (6 * q)
      (PowerSeries.X ^ ((j + w) * q + (j + e)) *
        PowerSeries.mk (fun x => ((d + x).choose d : Int))) =
      if j + w < 6 then affineChoose (6 - (j + w)) (d - (j + e)) d q else 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases hl : j + w < 6
  · have hsum : 6 * q = (j + w) * q + (6 - (j + w)) * q := by
      rw [← Nat.add_mul, Nat.add_sub_of_le hl.le]
    have hje : j + e ≤ d := by omega
    rw [if_pos hl]
    by_cases hb : (j + w) * q + (j + e) ≤ 6 * q
    · rw [if_pos hb, PowerSeries.coeff_mk, affineChoose]
      congr 2
      omega
    · rw [if_neg hb, affineChoose, Nat.choose_eq_zero_of_lt (by omega : (6 - (j + w)) * q + (d - (j + e)) < d)]
      simp
  · have hm := Nat.mul_le_mul_right q (show 6 ≤ j + w by omega)
    rw [if_neg hl, if_neg (by omega)]

private theorem coeff_signedRows (q n d w e : Nat) (hw : w ≤ 5) (hd : 5 + e ≤ d) :
    PowerSeries.coeff Int (6 * q)
      ((1 - PowerSeries.X ^ (q + 1)) ^ n * PowerSeries.X ^ (w * q + e) *
        PowerSeries.mk (fun x => ((d + x).choose d : Int))) = signedRows n d w e q := by
  rw [one_sub_X_pow_expansion, Finset.sum_mul, Finset.sum_mul, map_sum, signedRows, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc, mul_assoc, PowerSeries.coeff_C_mul,
    ← mul_assoc (PowerSeries.X ^ ((q + 1) * j)) (PowerSeries.X ^ (w * q + e)),
    ← pow_add,
    show (q + 1) * j + (w * q + e) = (j + w) * q + (j + e) by ring,
    coeff_shifted_choose q j w e d hw hd]
  by_cases hj : j + w < 6 <;> simp [hj, smul_eq_mul]

private theorem unsplitAllCounts : unsplitByCompositions = signedRows 10 10 0 0 - signedRows 10 10 2 1 := by
  funext q
  change (boundedCount (List.replicate 10 q ++ [2 * q]) (6 * q) : Int) = _
  rw [← boxSeries_coeff, boxSeries_append, boxSeries_replicate]
  simp only [boxSeries, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [capSeries_eq, capSeries_eq, mul_pow]
  have h :
      (1 - PowerSeries.X ^ (q + 1)) ^ 10 * (PowerSeries.mk 1 : PowerSeries Int) ^ 10 *
        ((1 - PowerSeries.X ^ (2 * q + 1)) * PowerSeries.mk 1) =
        (1 - PowerSeries.X ^ (q + 1)) ^ 10 * PowerSeries.X ^ (0 * q + 0) *
          (PowerSeries.mk 1 : PowerSeries Int) ^ 11 -
        (1 - PowerSeries.X ^ (q + 1)) ^ 10 * PowerSeries.X ^ (2 * q + 1) *
          (PowerSeries.mk 1 : PowerSeries Int) ^ 11 := by
    simp only [zero_mul, zero_add, pow_zero, mul_one]
    ring
  rw [h, PowerSeries.mk_one_pow_eq_mk_choose_add, map_sub,
    coeff_signedRows q 10 10 0 0 (by decide) (by decide),
    coeff_signedRows q 10 10 2 1 (by decide) (by decide)]
  rfl

private theorem splitAllCounts : splitByCompositions = signedRows 12 11 0 0 := by
  funext q
  change (boundedCount (List.replicate 12 q) (6 * q) : Int) = _
  rw [← boxSeries_coeff, boxSeries_replicate, capSeries_eq, mul_pow,
    PowerSeries.mk_one_pow_eq_mk_choose_add]
  have h := coeff_signedRows q 12 11 0 0 (by decide) (by decide)
  simpa only [zero_mul, zero_add, pow_zero, mul_one] using h

private theorem choose_difference (x a d : Nat) :
    ((x + a).choose (d + 1) : Int) - (x.choose (d + 1) : Int) =
      ∑ i ∈ Finset.range a, ((x + i).choose d : Int) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.add_succ, Nat.choose_succ_succ', Nat.cast_add, Finset.sum_range_succ, ← ih]
    ring

private theorem affineChoose_difference (a b d : Nat) :
    Δ_[1] (affineChoose a b (d + 1)) =
      ∑ i ∈ Finset.range a, affineChoose a (b + i) d := by
  funext q
  rw [fwdDiff, Finset.sum_apply, affineChoose, affineChoose]
  simp only [Nat.mul_add, Nat.mul_one]
  rw [show a * q + a + b = (a * q + b) + a by omega,
    choose_difference]
  simp only [affineChoose, Nat.add_assoc]

private theorem affineChoose_difference_zero (a b d : Nat) :
    Δ_[1]^[d + 1] (affineChoose a b d) = 0 := by
  induction d generalizing a b with
  | zero =>
    have h : affineChoose a b 0 = fun _ => 1 := by
      funext q
      simp [affineChoose]
    rw [h, Function.iterate_one, fwdDiff_const]
    rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply, affineChoose_difference, fwdDiff_iter_finset_sum]
    simp [ih]

private theorem signedRows_difference_zero (n d w e : Nat) :
    Δ_[1]^[d + 1] (signedRows n d w e) = 0 := by
  rw [signedRows, fwdDiff_iter_finset_sum]
  apply Finset.sum_eq_zero
  intro j _
  split
  · rw [fwdDiff_iter_const_smul, affineChoose_difference_zero, smul_zero]
  · exact Function.iterate_fixed (fwdDiff_const (M := Nat) (h := 1) (0 : Int)) (d + 1)

private theorem coeff_normalized_eq_diff (m q : Nat) (f : Nat → Int) :
    PowerSeries.coeff Int (q + m) ((1 - PowerSeries.X) ^ m * PowerSeries.mk f) =
      (Δ_[1]^[m] f) q := by
  induction m generalizing q with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc, sub_mul, one_mul, map_sub]
    have hshift : PowerSeries.coeff Int (q + (m + 1))
        (PowerSeries.X * ((1 - PowerSeries.X) ^ m * PowerSeries.mk f)) =
        PowerSeries.coeff Int (q + m) ((1 - PowerSeries.X) ^ m * PowerSeries.mk f) := by
      exact PowerSeries.coeff_succ_X_mul (q + m) _
    rw [hshift, show q + (m + 1) = (q + 1) + m by omega, ih, ih,
      Function.iterate_succ_apply', fwdDiff]

private theorem normalized_zero_above (d : Nat) (f : Nat → Int)
    (hdiff : Δ_[1]^[d + 1] f = 0) (i : Nat) (hi : d < i) :
    PowerSeries.coeff Int i (normalizedCountSeries d f) = 0 := by
  have hindex : i = (i - (d + 1)) + (d + 1) := (Nat.sub_add_cancel hi).symm
  rw [normalizedCountSeries, hindex, coeff_normalized_eq_diff, hdiff]
  rfl

private noncomputable def polynomialPrefix (d : Nat) (s : PowerSeries Int) : Polynomial Int :=
  ∑ i ∈ Finset.range (d + 1), Polynomial.C (PowerSeries.coeff Int i s) * Polynomial.X ^ i

private theorem coeff_polynomialPrefix (d i : Nat) (s : PowerSeries Int) :
    (polynomialPrefix d s).coeff i = if i ≤ d then PowerSeries.coeff Int i s else 0 := by
  rw [polynomialPrefix, Polynomial.finset_sum_coeff]
  simp [Polynomial.coeff_C_mul_X_pow, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_iff]

private theorem polynomialPrefix_degree (d : Nat) (s : PowerSeries Int) :
    (polynomialPrefix d s).natDegree ≤ d := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro i hi
  rw [coeff_polynomialPrefix, if_neg (not_le_of_gt hi)]

private theorem polynomialPrefix_series (d : Nat) (s : PowerSeries Int)
    (htail : ∀ i > d, PowerSeries.coeff Int i s = 0) :
    (polynomialPrefix d s : PowerSeries Int) = s := by
  ext i
  rw [Polynomial.coeff_coe, coeff_polynomialPrefix]
  by_cases hi : i ≤ d
  · rw [if_pos hi]
  · rw [if_neg hi, htail i (lt_of_not_ge hi)]

private noncomputable def unsplitCountSeries : PowerSeries Int :=
  normalizedCountSeries 10 (fun q => (integerPointCount unsplitCaps 6 q : Int))

private noncomputable def splitCountSeries : PowerSeries Int :=
  normalizedCountSeries 11 (fun q => (integerPointCount splitCaps 6 q : Int))

/-- Actual normalized lattice-count series for the unsplit prism. -/
noncomputable def unsplitEhrhartPolynomial : Polynomial Int := polynomialPrefix 10 unsplitCountSeries

/-- Actual normalized lattice-count series for the split prism. -/
noncomputable def splitEhrhartPolynomial : Polynomial Int := polynomialPrefix 11 splitCountSeries

theorem unsplitEhrhartSeries :
    (unsplitEhrhartPolynomial : PowerSeries Int) =
      normalizedCountSeries 10 (fun q => (integerPointCount unsplitCaps 6 q : Int)) := by
  apply polynomialPrefix_series
  intro i hi
  rw [unsplitCountSeries, unsplitIntegerCounts, unsplitAllCounts]
  apply normalized_zero_above _ _ _ i hi
  rw [sub_eq_add_neg, ← neg_one_smul ℤ, fwdDiff_iter_add,
    fwdDiff_iter_const_smul, signedRows_difference_zero, signedRows_difference_zero]
  simp

theorem splitEhrhartSeries :
    (splitEhrhartPolynomial : PowerSeries Int) =
      normalizedCountSeries 11 (fun q => (integerPointCount splitCaps 6 q : Int)) := by
  apply polynomialPrefix_series
  intro i hi
  rw [splitCountSeries, splitIntegerCounts, splitAllCounts]
  exact normalized_zero_above _ _ (signedRows_difference_zero _ _ _ _) i hi

/-- No additional existence or degree hypotheses about the Ehrhart series are required. -/
theorem ehrhartPolynomialsDoNotInterlace :
    ¬ ∃ ps qs : List ℝ,
      (∀ x : ℝ, x ∈ ps ↔ unsplitEhrhartPolynomial.eval₂ (Int.castRingHom ℝ) x = 0) ∧
      (∀ x : ℝ, x ∈ qs ↔ splitEhrhartPolynomial.eval₂ (Int.castRingHom ℝ) x = 0) ∧
      alternatingRoots ps qs :=
  integerPointSeriesPolynomialsDoNotInterlace _ _ unsplitEhrhartSeries splitEhrhartSeries
    (polynomialPrefix_degree _ _) (polynomialPrefix_degree _ _)

#print axioms unsplitEhrhartSeries
#print axioms splitEhrhartSeries
#print axioms ehrhartPolynomialsDoNotInterlace

end PrismSplit
