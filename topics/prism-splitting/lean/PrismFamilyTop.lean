import PrismFamilyReciprocity
import PrismFamily

namespace PrismFamily

open PrismSplit
open scoped BigOperators fwdDiff

private def extendZero (f : Nat → Int) (j : Int) : Int :=
  if 0 ≤ j then f j.toNat else 0

private theorem extendCoeff_sub_X (s : PowerSeries Int) (k : Int) :
    extendZero (fun j => PowerSeries.coeff Int j ((1 - PowerSeries.X) * s)) k =
      extendZero (fun j => PowerSeries.coeff Int j s) k -
      extendZero (fun j => PowerSeries.coeff Int j s) (k - 1) := by
  cases k with
  | ofNat k =>
    cases k with
    | zero =>
      change extendZero (fun j => PowerSeries.coeff Int j ((1 - PowerSeries.X) * s)) 0 = _
      simp [extendZero, sub_mul]
    | succ n =>
      change extendZero (fun j => PowerSeries.coeff Int j ((1 - PowerSeries.X) * s))
          ((n + 1 : Nat) : Int) =
        extendZero (fun j => PowerSeries.coeff Int j s) ((n + 1 : Nat) : Int) -
        extendZero (fun j => PowerSeries.coeff Int j s) (((n + 1 : Nat) : Int) - 1)
      rw [show ((n + 1 : Nat) : Int) - 1 = n by omega]
      have hn : (0 : Int) ≤ (n : Int) + 1 := by positivity
      simp [extendZero, sub_mul, hn]
  | negSucc n =>
    have hn : ¬0 ≤ Int.negSucc n := by omega
    have hn' : ¬0 ≤ Int.negSucc n - 1 := by omega
    simp [extendZero, hn, hn']

private theorem coeff_eq_extendDiff (m : Nat) (k : Int) (f : Nat → Int) :
    extendZero (fun j => PowerSeries.coeff Int j ((1 - PowerSeries.X) ^ m * PowerSeries.mk f)) k =
      (Δ_[1]^[m] (extendZero f)) (k - (m : Int)) := by
  induction m generalizing k with
  | zero => simp [extendZero]
  | succ m ih =>
    rw [pow_succ', mul_assoc, extendCoeff_sub_X, ih, ih, Function.iterate_succ_apply', fwdDiff]
    rw [show k - (m.succ : Int) + 1 = k - (m : Int) by omega,
      show k - (m.succ : Int) = k - 1 - (m : Int) by omega]

private theorem parity_difference (m i : Nat) (hi : i ≤ m) :
    (-1 : Int) ^ (m - i) = (-1 : Int) ^ m * (-1 : Int) ^ i := by
  have hsq : (-1 : Int) ^ i * (-1 : Int) ^ i = 1 := by
    rw [← mul_pow]
    norm_num
  conv_rhs => rw [show m = (m - i) + i by omega, pow_add]
  rw [mul_assoc, hsq, mul_one]

theorem coeff_from_reflection (d r : Nat) (F : Int → Int) (L I : Nat → Int)
    (hr : r ≤ d + 1) (hF : ∀ n : Nat, F (n : Int) = L n)
    (hzero : Δ_[1]^[d + 1] F = 0)
    (hI : ∀ n : Nat, 0 < n → (-1 : Int) ^ d * F (-(n : Int)) = I n) :
    PowerSeries.coeff Int (d + 1 - r) (normalizedCountSeries d L) =
      ∑ i ∈ Finset.range r, ((-1 : Int) ^ i * ((d + 1).choose i : Int)) * I (r - i) := by
  let negPart (k : Int) : Int := if k < 0 then F k else 0
  have hext : extendZero L = F - negPart := by
    funext k
    by_cases hk : 0 ≤ k
    · have hkn := Int.toNat_of_nonneg hk
      simp only [extendZero, hk, if_true, Pi.sub_apply, negPart, not_lt_of_ge hk, if_false, sub_zero]
      rw [← hF k.toNat, hkn]
    · have hn : k < 0 := lt_of_not_ge hk
      simp [extendZero, hk, negPart, hn]
  have heq := coeff_eq_extendDiff (d + 1) ((d + 1 - r : Nat) : Int) L
  simp only [extendZero, Nat.cast_nonneg, if_true, Int.toNat_natCast] at heq
  have hs :
      Δ_[1]^[d + 1] (extendZero L) = -(Δ_[1]^[d + 1] negPart) := by
    rw [hext, sub_eq_add_neg, ← neg_one_smul ℤ, fwdDiff_iter_add,
      fwdDiff_iter_const_smul, hzero, zero_add, neg_one_smul]
  rw [normalizedCountSeries, heq, hs,
    show (((d + 1 - r : Nat) : Int) - ((d + 1 : Nat) : Int)) = -(r : Int) by omega,
    Pi.neg_apply, fwdDiff_iter_eq_sum_shift]
  rw [← Finset.sum_subset (Finset.range_mono (show r ≤ d + 1 + 1 by omega))]
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hir : i < r := Finset.mem_range.mp hi
    have hd : i ≤ d + 1 := by omega
    have hx : -(r : Int) + i • (1 : Int) = -((r - i : Nat) : Int) := by
      simp only [nsmul_eq_mul, Nat.cast_one, mul_one]
      omega
    have hneg : -(r : Int) + i • (1 : Int) < 0 := by rw [hx]; omega
    simp only [negPart, if_pos hneg]
    rw [hx, smul_eq_mul, parity_difference _ _ hd, pow_succ,
      ← hI (r - i) (by omega)]
    ring
  · intro i _ hi
    have hir : r ≤ i := by
      have hn : ¬ i < r := fun h => hi (Finset.mem_range.mpr h)
      omega
    have hnonneg : ¬ -(r : Int) + i • (1 : Int) < 0 := by
      simp only [nsmul_eq_mul, mul_one]
      omega
    simp only [negPart, if_neg hnonneg, smul_zero]

private theorem capSeries_zero : capSeries 0 = 1 := by simp [capSeries]

private theorem capSeries_one : capSeries 1 = 1 + PowerSeries.X := by
  simp [capSeries, Finset.sum_range_succ]

private theorem boxSeries_singleton (c : Nat) : boxSeries [c] = capSeries c := by
  simp [boxSeries]

private theorem coeff_one_add_pow (n j : Nat) :
    PowerSeries.coeff Int j ((1 + PowerSeries.X : PowerSeries Int) ^ n) = (n.choose j : Int) := by
  have h : ((1 + PowerSeries.X : PowerSeries Int) ^ n) =
      ((((1 + Polynomial.X : Polynomial Int) ^ n) : Polynomial Int) : PowerSeries Int) := by simp
  rw [h, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

private theorem beforeInterior_two (b : Nat) : beforeInterior b 2 = 1 := by
  rw [beforeInterior, if_neg (by decide), ← boxSeries_coeff,
    boxSeries_append, boxSeries_replicate, boxSeries_singleton]
  rw [show (b + 1) * 2 - (2 * b + 1) = 1 by omega]
  norm_num [capSeries_zero, capSeries, Finset.sum_range_succ, PowerSeries.coeff_X_pow, add_comm]

private theorem afterInterior_two (b : Nat) : afterInterior b 2 = 1 := by
  rw [afterInterior, if_neg (by decide), ← boxSeries_coeff, boxSeries_replicate]
  rw [show (b + 1) * 2 - (2 * b + 2) = 0 by omega]
  norm_num [capSeries_zero]

private theorem beforeInterior_three (b : Nat) (hb : 2 ≤ b) :
    beforeInterior b 3 = ((2 * b).choose b : Int) + 2 * ((2 * b).choose (b + 1) : Int) +
      2 * ((2 * b).choose (b + 2) : Int) := by
  rw [beforeInterior, if_neg (by decide), ← boxSeries_coeff, boxSeries_append,
    boxSeries_replicate, boxSeries_singleton]
  rw [show (b + 1) * 3 - (2 * b + 1) = b + 2 by omega]
  change PowerSeries.coeff Int (b + 2) (capSeries 1 ^ (2 * b) * capSeries 4) = _
  rw [capSeries_one, capSeries, Finset.mul_sum, map_sum]
  simp_rw [PowerSeries.coeff_mul_X_pow', coeff_one_add_pow]
  have hs1 : (2 * b).choose (b - 1) = (2 * b).choose (b + 1) := by
    have h := Nat.choose_symm (n := 2 * b) (k := b - 1) (by omega)
    simpa only [show 2 * b - (b - 1) = b + 1 by omega] using h.symm
  have hs2 : (2 * b).choose (b - 2) = (2 * b).choose (b + 2) := by
    have h := Nat.choose_symm (n := 2 * b) (k := b - 2) (by omega)
    simpa only [show 2 * b - (b - 2) = b + 2 by omega] using h.symm
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    show (0 : Nat) ≤ b + 2 by omega, show (1 : Nat) ≤ b + 2 by omega,
    show (2 : Nat) ≤ b + 2 by omega, show (3 : Nat) ≤ b + 2 by omega,
    show (4 : Nat) ≤ b + 2 by omega, if_true, Nat.sub_zero, add_zero,
    show b + 2 - 1 = b + 1 by omega, show b + 2 - 2 = b by omega,
    show b + 2 - 3 = b - 1 by omega, show b + 2 - 4 = b - 2 by omega, hs1, hs2]
  ring

private theorem afterInterior_three (b : Nat) :
    afterInterior b 3 = ((2 * b + 2).choose (b + 1) : Int) := by
  rw [afterInterior, if_neg (by decide), ← boxSeries_coeff, boxSeries_replicate,
    show (b + 1) * 3 - (2 * b + 2) = b + 1 by omega]
  change PowerSeries.coeff Int (b + 1) (capSeries 1 ^ (2 * b + 2)) = _
  rw [capSeries_one, coeff_one_add_pow]

private theorem nextCoeff_from_reflection (d : Nat) (F : Int → Int) (L I : Nat → Int)
    (p : Polynomial Int) (hd : 2 ≤ d) (hp : p.natDegree ≤ d)
    (hpSeries : (p : PowerSeries Int) = normalizedCountSeries d L)
    (hF : ∀ n : Nat, F (n : Int) = L n)
    (hzero : Δ_[1]^[d + 1] F = 0)
    (hI : ∀ n : Nat, 0 < n → (-1 : Int) ^ d * F (-(n : Int)) = I n)
    (hI1 : I 1 = 0) (hI2 : I 2 = 1) :
    p.Monic ∧ p.natDegree = d - 1 ∧ p.nextCoeff = I 3 - (d + 1 : Nat) := by
  have hcoef (r : Nat) (hr : r ≤ d + 1) :
      p.coeff (d + 1 - r) =
        ∑ i ∈ Finset.range r, ((-1 : Int) ^ i * ((d + 1).choose i : Int)) * I (r - i) := by
    rw [← Polynomial.coeff_coe, hpSeries]
    exact coeff_from_reflection d r F L I hr hF hzero hI
  have h1 := hcoef 1 (by omega)
  have h2 := hcoef 2 (by omega)
  have h3 := hcoef 3 (by omega)
  have hz : p.coeff d = 0 := by
    simpa [hI1] using h1
  have hl : p.coeff (d - 1) = 1 := by
    simpa [Finset.sum_range_succ, hI1, hI2,
      show d + 1 - 2 = d - 1 by omega] using h2
  have hn : p.coeff (d - 2) = I 3 - (d + 1 : Nat) := by
    simpa [Finset.sum_range_succ, hI1, hI2, sub_eq_add_neg,
      show d + 1 - 3 = d - 2 by omega] using h3
  have hdeg : p.natDegree = d - 1 := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro n hn
      by_cases h : n = d
      · simpa only [h] using hz
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    · rw [hl]
      decide
  refine ⟨?_, hdeg, ?_⟩
  · rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg, hl]
  · simpa [Polynomial.nextCoeff, hdeg, show d - 1 - 1 = d - 2 by omega,
      show d - 1 ≠ 0 by omega] using hn

theorem beforeNumerator_top (b : Nat) (hb : 2 ≤ b) :
    (beforeNumerator b).Monic ∧ (beforeNumerator b).natDegree = 2 * b - 1 ∧
      (beforeNumerator b).nextCoeff = before b := by
  have h := nextCoeff_from_reflection (2 * b) (beforeIntExtension b) (beforeCounts b)
    (beforeInterior b) (beforeNumerator b) (by omega) (polynomialPrefix_degree _ _)
    (beforeNumeratorSeries b hb) (fun n => beforeIntExtension_nat b n hb)
    (beforeIntExtension_diff b) (fun n hn => beforeInterior_reflection b n hb hn)
    (by simp [beforeInterior]) (beforeInterior_two b)
  rw [beforeInterior_three b hb] at h
  simpa [before, Nat.cast_add, Nat.cast_mul] using h

theorem afterNumerator_top (b : Nat) (hb : 2 ≤ b) :
    (afterNumerator b).Monic ∧ (afterNumerator b).natDegree = 2 * b ∧
      (afterNumerator b).nextCoeff = after b := by
  have h := nextCoeff_from_reflection (2 * b + 1) (afterIntExtension b) (afterCounts b)
    (afterInterior b) (afterNumerator b) (by omega) (polynomialPrefix_degree _ _)
    (afterNumeratorSeries b) (afterIntExtension_nat b)
    (afterIntExtension_diff b) (fun n hn => afterInterior_reflection b n hb hn)
    (by simp [afterInterior]) (afterInterior_two b)
  rw [afterInterior_three b] at h
  simpa [after, Nat.cast_add, Nat.cast_mul] using h

theorem nextCoeff_map_int_real (p : Polynomial Int) :
    (p.map (Int.castRingHom ℝ)).nextCoeff = (p.nextCoeff : ℝ) := by
  have hinj : Function.Injective (Int.castRingHom ℝ) := Int.cast_injective
  simp [Polynomial.nextCoeff, Polynomial.natDegree_map_eq_of_injective hinj]

theorem familyNumeratorsDoNotAlternate (b : Nat) (hb : 6 ≤ b)
    (sp : ((beforeNumerator b).map (Int.castRingHom ℝ)).Splits (RingHom.id ℝ))
    (sq : ((afterNumerator b).map (Int.castRingHom ℝ)).Splits (RingHom.id ℝ)) :
    ¬ ∃ xs ys : List ℝ,
      (xs : Multiset ℝ) = ((beforeNumerator b).map (Int.castRingHom ℝ)).roots ∧
      (ys : Multiset ℝ) = ((afterNumerator b).map (Int.castRingHom ℝ)).roots ∧
      AlternatingNegative xs ys := by
  obtain ⟨hp, _, hpnext⟩ := beforeNumerator_top b (by omega)
  obtain ⟨hq, _, hqnext⟩ := afterNumerator_top b (by omega)
  exact polynomial_obstruction b hb _ _ (hp.map _) (hq.map _) sp sq
    (by rw [nextCoeff_map_int_real, hpnext])
    (by rw [nextCoeff_map_int_real, hqnext])

#print axioms beforeNumerator_top
#print axioms afterNumerator_top
#print axioms familyNumeratorsDoNotAlternate

end PrismFamily
