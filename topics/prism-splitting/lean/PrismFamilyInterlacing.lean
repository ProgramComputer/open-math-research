import PrismFamilyGeometry
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.SpecificLimits.Normed

namespace PrismFamily

open PrismSplit
open scoped BigOperators fwdDiff

private theorem count_binomial_expansion (d n : Nat) (f : Nat → Int) (p : Polynomial Int)
    (hp : p.natDegree ≤ d) (hSeries : (p : PowerSeries Int) = normalizedCountSeries d f) :
    f n = ∑ j ∈ Finset.range (d + 1), p.coeff j *
      (if j ≤ n then (((d + (n - j)).choose d : Nat) : Int) else 0) := by
  let geo : PowerSeries Int := PowerSeries.mk (fun k => ((d + k).choose d : Int))
  have hInv : (1 - PowerSeries.X : PowerSeries Int) ^ (d + 1) * geo = 1 :=
    (mul_comm _ _).trans (PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one Int d)
  have hProd : (PowerSeries.mk f : PowerSeries Int) = (p : PowerSeries Int) * geo := by
    rw [hSeries, normalizedCountSeries]
    calc
      _ = (PowerSeries.mk f : PowerSeries Int) * ((1 - PowerSeries.X) ^ (d + 1) * geo) := by
        rw [hInv, mul_one]
      _ = _ := by ring
  have hP : (p : PowerSeries Int) =
      ∑ j ∈ Finset.range (d + 1), PowerSeries.C Int (p.coeff j) * PowerSeries.X ^ j := by
    have hs := congrArg (Polynomial.coeToPowerSeries.ringHom (R := Int))
      (p.as_sum_range' (d + 1) (by omega))
    simpa only [map_sum, Polynomial.coeToPowerSeries.ringHom_apply,
      ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_pow, Polynomial.coe_X] using hs
  rw [← PowerSeries.coeff_mk n f, hProd, hP, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  simp only [geo, PowerSeries.coeff_mk]

private theorem hasSum_shifted_choose (d j : Nat) {x : ℝ} (hx : ‖x‖ < 1) :
    HasSum
      (fun n : Nat => if j ≤ n then ((d + (n - j)).choose d : ℝ) * x ^ n else 0)
      (x ^ j / (1 - x) ^ (d + 1)) := by
  let g (n : Nat) : ℝ := if j ≤ n then ((d + (n - j)).choose d : ℝ) * x ^ n else 0
  have ht : HasSum (fun n => g (n + j)) (x ^ j / (1 - x) ^ (d + 1)) := by
    have h := (hasSum_choose_mul_geometric_of_norm_lt_one d hx).mul_right (x ^ j)
    convert h using 1
    · funext n
      simp only [g, if_pos (Nat.le_add_left j n), Nat.add_sub_cancel, pow_add]
      rw [Nat.add_comm d n, mul_assoc]
    · ring
  have hh := (hasSum_nat_add_iff j).mp ht
  have hz : ∑ i ∈ Finset.range j, g i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact if_neg (not_le_of_gt (Finset.mem_range.mp hi))
  simpa only [hz, add_zero] using hh

private theorem hasSum_from_normalized (d : Nat) (f : Nat → Int) (p : Polynomial Int)
    (hp : p.natDegree ≤ d) (hSeries : (p : PowerSeries Int) = normalizedCountSeries d f)
    {x : ℝ} (hx : ‖x‖ < 1) :
    HasSum (fun n : Nat => (f n : ℝ) * x ^ n)
      (p.eval₂ (Int.castRingHom ℝ) x / (1 - x) ^ (d + 1)) := by
  have h := hasSum_sum (s := Finset.range (d + 1)) fun j _ =>
    (hasSum_shifted_choose d j hx).mul_left (p.coeff j : ℝ)
  convert h using 1
  · funext n
    rw [count_binomial_expansion d n f p hp hSeries]
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    split <;> simp [mul_assoc]
  · rw [Polynomial.eval₂_eq_sum_range' _ (by omega : p.natDegree < d + 1) x]
    simp only [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    change (p.coeff j : ℝ) * x ^ j * ((1 - x) ^ (d + 1))⁻¹ = _
    ring

private theorem normalized_eval_positive (d : Nat) (f : Nat → Int) (p : Polynomial Int)
    (hp : p.natDegree ≤ d) (hSeries : (p : PowerSeries Int) = normalizedCountSeries d f)
    (hnonneg : ∀ n, 0 ≤ f n) (hzero : 0 < f 0) {x : ℝ} (hx : 0 < x) (h1 : x < 1) :
    0 < p.eval₂ (Int.castRingHom ℝ) x := by
  have hnorm : ‖x‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hx]
  have h := hasSum_from_normalized d f p hp hSeries hnorm
  have hsum : 0 < ∑' n : Nat, (f n : ℝ) * x ^ n :=
    h.summable.tsum_pos (fun n => mul_nonneg (by exact_mod_cast hnonneg n) (pow_nonneg hx.le _)) 0
      (by simpa only [pow_zero, mul_one] using (show (0 : ℝ) < (f 0 : ℝ) by exact_mod_cast hzero))
  rw [h.tsum_eq] at hsum
  exact (div_pos_iff_of_pos_right (pow_pos (sub_pos.mpr h1) _)).mp hsum

private theorem afterCounts_zero (b : Nat) : afterCounts b 0 = 1 := by
  simp only [afterCounts, integerPointCount, cardinality_eq_boundedCount, afterCaps, dilatedCaps,
    List.map_replicate, zero_mul]
  rw [← boxSeries_coeff, boxSeries_replicate]
  simp [capSeries]

private theorem after_positive_small (b : Nat) {x : ℝ} (hx : 0 < x) (h1 : x < 1) :
    0 < (afterNumerator b).eval₂ (Int.castRingHom ℝ) x :=
  normalized_eval_positive _ _ _ (polynomialPrefix_degree _ _) (afterNumeratorSeries b)
    (fun _ => Int.natCast_nonneg _) (by rw [afterCounts_zero]; decide) hx h1


private theorem coeff_normalized_sum (d k : Nat) (f : Nat → Int) (hk : k ≤ d + 1) :
    PowerSeries.coeff Int k (normalizedCountSeries d f) =
      ∑ i ∈ Finset.range (k + 1), ((-1 : Int) ^ i * ((d + 1).choose i : Int)) * f (k - i) := by
  have h := one_sub_X_pow_expansion 1 (d + 1)
  simp only [pow_one, one_mul] at h
  rw [normalizedCountSeries, h, Finset.sum_mul, map_sum]
  simp only [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk]
  rw [← Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hk))]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
  · intro i _ hi
    have hne : ¬i ≤ k := fun h => hi (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
    simp only [if_neg hne, mul_zero]

private theorem afterInterior_translate (b q : Nat) :
    afterInterior b (q + 2) = afterCounts b q := by
  simp only [afterInterior, if_neg (show ¬q + 2 < 2 by omega), Nat.add_sub_cancel,
    afterCounts, integerPointCount, cardinality_eq_boundedCount, afterCaps, dilatedCaps,
    List.map_replicate, mul_one]
  rw [Nat.mul_add, show (b + 1) * 2 = 2 * b + 2 by omega, Nat.add_sub_cancel, mul_comm q]

theorem afterNumerator_reflect (b : Nat) (hb : 2 ≤ b) :
    Polynomial.reflect (2 * b) (afterNumerator b) = afterNumerator b := by
  ext k
  rw [Polynomial.coeff_reflect]
  by_cases hk : k ≤ 2 * b
  · rw [Polynomial.revAt_le hk]
    have h := coeff_from_reflection (2 * b + 1) (k + 2) (afterIntExtension b)
      (afterCounts b) (afterInterior b) (by omega) (afterIntExtension_nat b)
      (afterIntExtension_diff b) (fun n hn => afterInterior_reflection b n hb hn)
    rw [← afterNumeratorSeries b, Polynomial.coeff_coe,
      show 2 * b + 1 + 1 - (k + 2) = 2 * b - k by omega] at h
    rw [h, ← Polynomial.coeff_coe, afterNumeratorSeries,
      coeff_normalized_sum _ _ _ (by omega), Finset.sum_range_succ]
    have hfirst : afterInterior b 1 = 0 := by simp [afterInterior]
    simp only [show k + 2 - (k + 1) = 1 by omega, hfirst, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    -- Put the translated term back into the form of the strict-bound count.
    rw [show k + 2 - i = k - i + 2 by omega]
    exact congrArg (fun c : Int => ((-1 : Int) ^ i * ((2 * b + 2).choose i : Int)) * c)
      (afterInterior_translate b (k - i))
  · rw [Polynomial.revAt_eq_self_of_lt (lt_of_not_ge hk)]

theorem afterNumerator_no_root_gt_one (b : Nat) (hb : 2 ≤ b) {x : ℝ} (hx : 1 < x) :
    (afterNumerator b).eval₂ (Int.castRingHom ℝ) x ≠ 0 := by
  have hpos : 0 < x := by linarith
  letI := invertibleOfNonzero hpos.ne'
  have he := Polynomial.eval₂_reflect_mul_pow (Int.castRingHom ℝ) x (2 * b)
    (afterNumerator b) (by rw [(afterNumerator_top b hb).2.1])
  rw [afterNumerator_reflect b hb, invOf_eq_inv] at he
  have hsmall := after_positive_small b (inv_pos.mpr hpos) (inv_lt_one_of_one_lt₀ hx)
  rw [← he]
  exact (mul_pos hsmall (pow_pos hpos _)).ne'

private theorem alternating_sum_bound {ps qs : List ℝ} (h : alternatingRoots ps qs)
    (hbound : ∀ x ∈ qs, x ≤ 1) : -ps.sum - (-qs.sum) ≤ 1 := by
  induction ps generalizing qs with
  | nil =>
    cases qs with
    | nil => simp [alternatingRoots] at h
    | cons x xs =>
      cases xs with
      | nil => simpa using hbound x (by simp)
      | cons y ys => simp [alternatingRoots] at h
  | cons p ps ih =>
    cases qs with
    | nil => simp [alternatingRoots] at h
    | cons q qs =>
      cases qs with
      | nil => simp [alternatingRoots] at h
      | cons r rs =>
        obtain ⟨hqp, _, ht⟩ := h
        have hh := ih ht (fun x hx => hbound x (List.mem_cons_of_mem q hx))
        simp only [List.sum_cons] at hh ⊢
        linarith

theorem familyNumeratorsDoNotInterlace (b : Nat) (hb : 6 ≤ b)
    (sp : ((beforeNumerator b).map (Int.castRingHom ℝ)).Splits (RingHom.id ℝ))
    (sq : ((afterNumerator b).map (Int.castRingHom ℝ)).Splits (RingHom.id ℝ)) :
    ¬ ∃ xs ys : List ℝ,
      (xs : Multiset ℝ) = ((beforeNumerator b).map (Int.castRingHom ℝ)).roots ∧
      (ys : Multiset ℝ) = ((afterNumerator b).map (Int.castRingHom ℝ)).roots ∧
      alternatingRoots xs ys := by
  rintro ⟨xs, ys, hxs, hys, halt⟩
  obtain ⟨hp, _, hpc⟩ := beforeNumerator_top b (by omega)
  obtain ⟨hq, _, hqc⟩ := afterNumerator_top b (by omega)
  have hpMonic := hp.map (Int.castRingHom ℝ)
  have hqMonic := hq.map (Int.castRingHom ℝ)
  have hy : ∀ y ∈ ys, y ≤ 1 := by
    intro y hy
    by_contra! hgt
    have hm : y ∈ ((afterNumerator b).map (Int.castRingHom ℝ)).roots := by
      rw [← hys]
      exact hy
    have hr := (Polynomial.mem_roots hqMonic.ne_zero).mp hm
    exact afterNumerator_no_root_gt_one b (by omega) hgt (by
      simpa only [Polynomial.IsRoot, Polynomial.eval_map] using hr)
  have hvp := Polynomial.sum_roots_eq_nextCoeff_of_monic_of_split hpMonic sp
  have hvq := Polynomial.sum_roots_eq_nextCoeff_of_monic_of_split hqMonic sq
  rw [← hxs, nextCoeff_map_int_real, hpc] at hvp
  rw [← hys, nextCoeff_map_int_real, hqc] at hvq
  have hxp : -xs.sum = (before b : ℝ) := by simpa using hvp.symm
  have hxp' : -ys.sum = (after b : ℝ) := by simpa using hvq.symm
  have hbound := alternating_sum_bound halt hy
  rw [hxp, hxp'] at hbound
  have hgap : (after b : ℝ) + 1 < (before b : ℝ) := by
    exact_mod_cast coefficient_gap_beyond_one b hb
  linarith

/-- Weakly interlacing real-root multisets, with the second polynomial having the extra root. -/
def WeakRealInterlaces (p q : Polynomial Int) : Prop :=
  let P := p.map (Int.castRingHom ℝ)
  let Q := q.map (Int.castRingHom ℝ)
  P.Splits (RingHom.id ℝ) ∧ Q.Splits (RingHom.id ℝ) ∧
    ∃ xs ys : List ℝ, (xs : Multiset ℝ) = P.roots ∧ (ys : Multiset ℝ) = Q.roots ∧
      alternatingRoots xs ys

/-- The actual finite-coordinate box slices at level b+1 have
noninterlacing Ehrhart numerators for every b ≥ 6. -/
theorem familyBoxSplitCounterexample (b : Nat) (hb : 6 ≤ b) :
    ∃ p q : Polynomial Int,
      p.natDegree = 2 * b - 1 ∧ q.natDegree = 2 * b ∧
      (p : PowerSeries Int) = normalizedCountSeries
        (Module.finrank ℝ (affineSpan ℝ (realFinSlice (beforeFinCaps b) (b + 1))).direction)
        (fun i => (finLatticeCount (beforeFinCaps b) (b + 1) i (beforeFinNonempty b) : Int)) ∧
      (q : PowerSeries Int) = normalizedCountSeries
        (Module.finrank ℝ (affineSpan ℝ (realFinSlice (afterFinCaps b) (b + 1))).direction)
        (fun i => (finLatticeCount (afterFinCaps b) (b + 1) i (afterFinNonempty b) : Int)) ∧
      ¬ WeakRealInterlaces p q := by
  refine ⟨beforeNumerator b, afterNumerator b, (beforeNumerator_top b (by omega)).2.1,
    (afterNumerator_top b (by omega)).2.1, beforeFinSeries b (by omega), afterFinSeries b, ?_⟩
  rintro ⟨sp, sq, h⟩
  exact familyNumeratorsDoNotInterlace b hb sp sq h

#print axioms afterNumerator_reflect
#print axioms afterNumerator_no_root_gt_one
#print axioms familyNumeratorsDoNotInterlace
#print axioms familyBoxSplitCounterexample
end PrismFamily
