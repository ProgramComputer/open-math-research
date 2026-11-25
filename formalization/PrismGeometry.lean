import PrismCounts
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.PowerSeries.Basic

/-!
Integer points of the real prism slices corresponding to the exact split
counterexample, and noninterlacing of numerators defined from their counts.
-/

namespace PrismSplit

/-- Real ordered coordinate lists satisfying the bounds and the sum equation.
The pairwise bound relation also fixes the number of coordinates. -/
def realCoordinateSlice (caps : List Nat) (total : Nat) : Set (List ℝ) :=
  {x | List.Forall₂ (fun (a : ℝ) (c : Nat) => 0 ≤ a ∧ a ≤ (c : ℝ)) x caps ∧ x.sum = (total : ℝ)}

/-- The integer points subject to the same inequalities and sum equation. -/
def integerCoordinateSlice (caps : List Nat) (total : Nat) : Set (List Int) :=
  {x | List.Forall₂ (fun (a : Int) (c : Nat) => 0 ≤ a ∧ a ≤ (c : Int)) x caps ∧ x.sum = (total : Int)}

def dilatedCaps (caps : List Nat) (q : Nat) : List Nat := caps.map (q * ·)

private theorem sum_atoms_cast_int (v : List Nat) :
    (v.map Int.ofNat).sum = (v.sum : Int) := by
  induction v with
  | nil => rfl
  | cons a v ih => simp [ih]

private theorem sum_atoms_cast_real (v : List Int) :
    (v.map (fun (a : Int) => (a : ℝ))).sum = (v.sum : ℝ) := by
  induction v with
  | nil => simp only [List.map_nil, List.sum_nil, Int.cast_zero]
  | cons a v ih => simp only [List.map_cons, List.sum_cons, ih, Int.cast_add]

theorem integerCoordinateSlice_iff_real (caps : List Nat) (total : Nat) (v : List Int) :
    v ∈ integerCoordinateSlice caps total ↔
      v.map (fun (a : Int) => (a : ℝ)) ∈ realCoordinateSlice caps total := by
  change (List.Forall₂ (fun (a : Int) (c : Nat) => 0 ≤ a ∧ a ≤ (c : Int)) v caps ∧ v.sum = (total : Int)) ↔
      (List.Forall₂ (fun (a : ℝ) (c : Nat) => 0 ≤ a ∧ a ≤ (c : ℝ)) (v.map (fun (a : Int) => (a : ℝ))) caps ∧
        (v.map (fun (a : Int) => (a : ℝ))).sum = (total : ℝ))
  rw [List.forall₂_map_left_iff, sum_atoms_cast_real]
  constructor
  · rintro ⟨hBounds, hSum⟩
    refine ⟨hBounds.imp ?_, ?_⟩
    · intro a c h
      exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
    · exact_mod_cast hSum
  · rintro ⟨hBounds, hSum⟩
    refine ⟨hBounds.imp ?_, ?_⟩
    · intro a c h
      exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
    · exact_mod_cast hSum

private theorem natural_bounds_of_integer {v : List Int} {caps : List Nat}
    (h : List.Forall₂ (fun (a : Int) (c : Nat) => 0 ≤ a ∧ a ≤ (c : Int)) v caps) :
    List.Forall₂ (· ≤ ·) (v.map Int.toNat) caps := by
  rw [List.forall₂_map_left_iff]
  apply h.imp
  intro a c hab
  omega

private theorem integer_bounds_of_natural {v caps : List Nat}
    (h : List.Forall₂ (· ≤ ·) v caps) :
    List.Forall₂ (fun (a : Int) (c : Nat) => 0 ≤ a ∧ a ≤ (c : Int)) (v.map Int.ofNat) caps := by
  rw [List.forall₂_map_left_iff]
  apply h.imp
  intro a c hab
  change 0 ≤ (a : Int) ∧ (a : Int) ≤ (c : Int)
  exact ⟨Int.natCast_nonneg _, by exact_mod_cast hab⟩

private theorem cast_toNat_map_of_bounds {v : List Int} {caps : List Nat}
    (h : List.Forall₂ (fun (a : Int) (c : Nat) => 0 ≤ a ∧ a ≤ (c : Int)) v caps) :
    (v.map Int.toNat).map Int.ofNat = v := by
  induction h with
  | nil => rfl
  | cons hBounds _ ih =>
    simpa only [List.map_cons, ih, Int.ofNat_eq_coe] using
      congrArg (fun a => a :: _) (Int.toNat_of_nonneg hBounds.1)

/-- Taking each coordinate to its natural value gives a bijection. -/
def integerPointEquiv (caps : List Nat) (total : Nat) :
    integerCoordinateSlice caps total ≃
      {v : List Nat // v ∈ boundedCompositions caps total} where
  toFun x :=
    ⟨x.val.map Int.toNat, mem_boundedCompositions.mpr (by
      have hb := x.property.1
      have hs : x.val.sum = (total : Int) := x.property.2
      refine ⟨natural_bounds_of_integer hb, ?_⟩
      have hc := cast_toNat_map_of_bounds hb
      have hsum : (((x.val.map Int.toNat).sum : Nat) : Int) = (total : Int) := by
        rw [← sum_atoms_cast_int, hc, hs]
      exact_mod_cast hsum)⟩
  invFun y :=
    ⟨y.val.map Int.ofNat, by
      obtain ⟨hb, hs⟩ := mem_boundedCompositions.mp y.property
      exact ⟨integer_bounds_of_natural hb, by rw [sum_atoms_cast_int, hs]⟩⟩
  left_inv x := Subtype.ext (cast_toNat_map_of_bounds x.property.1)
  right_inv y := by
    apply Subtype.ext
    change (y.val.map Int.ofNat).map Int.toNat = y.val
    rw [List.map_map]
    simp [Function.comp_def]

private def boundedCompositionFintype (caps : List Nat) (total : Nat) :
    Fintype {v : List Nat // v ∈ boundedCompositions caps total} :=
  Fintype.subtype (boundedCompositions caps total).toFinset
    (fun _ => List.mem_toFinset)

instance integerCoordinateSliceFintype (caps : List Nat) (total : Nat) :
    Fintype (integerCoordinateSlice caps total) := by
  letI := boundedCompositionFintype caps total
  exact Fintype.ofEquiv _ (integerPointEquiv caps total).symm

/-- The dilation uses the scaled bounds and target sum. -/
def integerPointCount (caps : List Nat) (total q : Nat) : Nat :=
  Fintype.card (integerCoordinateSlice (dilatedCaps caps q) (q * total))

theorem cardinality_eq_boundedCount (caps : List Nat) (total : Nat) :
    Fintype.card (integerCoordinateSlice caps total) = boundedCount caps total := by
  letI := boundedCompositionFintype caps total
  refine (Fintype.card_congr (integerPointEquiv caps total)).trans ?_
  rw [boundedCount_eq_length, ← List.toFinset_card_of_nodup (boundedCompositions_nodup caps total)]
  exact Fintype.card_of_subtype _ (fun _ => List.mem_toFinset)

def unsplitCaps : List Nat := List.replicate 10 1 ++ [2]
def splitCaps : List Nat := List.replicate 12 1

theorem unsplitIntegerCounts :
    (fun q : Nat => (integerPointCount unsplitCaps 6 q : Int)) = unsplitByCompositions := by
  funext q
  simp [integerPointCount, cardinality_eq_boundedCount, unsplitCaps, dilatedCaps,
    unsplitByCompositions, Nat.mul_comm]

theorem splitIntegerCounts :
    (fun q : Nat => (integerPointCount splitCaps 6 q : Int)) = splitByCompositions := by
  funext q
  simp [integerPointCount, cardinality_eq_boundedCount, splitCaps, dilatedCaps,
    splitByCompositions, Nat.mul_comm]

private theorem real_sum_mul (r : ℝ) (xs : List ℝ) :
    (xs.map (r * ·)).sum = r * xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, mul_add]

private theorem real_sum_div (r : ℝ) (xs : List ℝ) :
    (xs.map (· / r)).sum = xs.sum / r := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, add_div]

private theorem zero_coordinate_list {x : List ℝ} {caps : List Nat}
    (h : List.Forall₂ (fun (a : ℝ) (_ : Nat) => 0 ≤ a ∧ a ≤ 0) x caps) :
    x = List.replicate caps.length 0 := by
  induction h with
  | nil => rfl
  | cons hbound _ ih =>
    simp [le_antisymm hbound.2 hbound.1, ih, List.replicate_succ]

/-- Scaling the inequalities and the prescribed sum describes geometric dilation.
The nonempty hypothesis also covers dilation by zero. -/
theorem realSliceDilation (caps : List Nat) (total q : Nat)
    (hne : (realCoordinateSlice caps total).Nonempty) :
    realCoordinateSlice (dilatedCaps caps q) (q * total) =
      (fun xs : List ℝ => xs.map ((q : ℝ) * ·)) '' realCoordinateSlice caps total := by
  ext x
  constructor
  · intro hx
    have hb := hx.1
    have hs := hx.2
    simp only [dilatedCaps, List.forall₂_map_right_iff, Nat.cast_mul] at hb hs
    by_cases hq : q = 0
    · subst q
      obtain ⟨w, hw⟩ := hne
      refine ⟨w, hw, ?_⟩
      have hlen := hw.1.length_eq
      have hz : x = List.replicate caps.length 0 :=
        zero_coordinate_list (by simpa only [Nat.cast_zero, zero_mul] using hb)
      change w.map (((0 : Nat) : ℝ) * ·) = x
      simpa only [Nat.cast_zero, zero_mul, List.map_const', hlen] using hz.symm
    · have hpos : (0 : ℝ) < (q : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hq
      refine ⟨x.map (· / (q : ℝ)), ?_, ?_⟩
      · change List.Forall₂ (fun (a : ℝ) (c : Nat) => 0 ≤ a ∧ a ≤ (c : ℝ))
          (x.map (· / (q : ℝ))) caps ∧ (x.map (· / (q : ℝ))).sum = (total : ℝ)
        refine ⟨List.forall₂_map_left_iff.mpr (hb.imp ?_), ?_⟩
        · intro a c hab
          exact ⟨div_nonneg hab.1 hpos.le, (div_le_iff₀' hpos).mpr hab.2⟩
        · rw [real_sum_div, hs, mul_div_cancel_left₀ _ hpos.ne']
      · change (x.map (· / (q : ℝ))).map ((q : ℝ) * ·) = x
        rw [List.map_map]
        simp only [Function.comp_def]
        have hmap : (fun a : ℝ => (q : ℝ) * (a / (q : ℝ))) = id := by
          funext a
          calc
            _ = (q : ℝ) * a / (q : ℝ) := (mul_div_assoc _ _ _).symm
            _ = a := mul_div_cancel_left₀ _ hpos.ne'
        rw [hmap, List.map_id]
  · rintro ⟨w, hw, rfl⟩
    change List.Forall₂ (fun (a : ℝ) (c : Nat) => 0 ≤ a ∧ a ≤ (c : ℝ))
        (w.map ((q : ℝ) * ·)) (dilatedCaps caps q) ∧
      (w.map ((q : ℝ) * ·)).sum = ((q * total : Nat) : ℝ)
    have hq : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
    rw [dilatedCaps, List.forall₂_map_right_iff, List.forall₂_map_left_iff,
      real_sum_mul, Nat.cast_mul, hw.2]
    refine ⟨hw.1.imp ?_, rfl⟩
    intro a c hab
    refine ⟨mul_nonneg hq hab.1, ?_⟩
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left hab.2 hq

private theorem sum_natural_cast_real (v : List Nat) :
    (v.map (fun (a : Nat) => (a : ℝ))).sum = (v.sum : ℝ) := by
  induction v with
  | nil => simp only [List.map_nil, List.sum_nil, Nat.cast_zero]
  | cons a v ih => simp only [List.map_cons, List.sum_cons, ih, Nat.cast_add]

theorem realSliceNonempty_of_double_sum (caps : List Nat) (total : Nat)
    (h : caps.sum = 2 * total) : (realCoordinateSlice caps total).Nonempty := by
  refine ⟨caps.map (fun (c : Nat) => (c : ℝ) / 2), ?_⟩
  change List.Forall₂ (fun (a : ℝ) (c : Nat) => 0 ≤ a ∧ a ≤ (c : ℝ))
      (caps.map (fun (c : Nat) => (c : ℝ) / 2)) caps ∧
    (caps.map (fun (c : Nat) => (c : ℝ) / 2)).sum = (total : ℝ)
  refine ⟨?_, ?_⟩
  · rw [List.forall₂_map_left_iff]
    have hc : List.Forall₂ (fun a b : Nat => a = b) caps caps := List.forall₂_refl caps
    apply hc.imp
    intro c d hcd
    subst d
    have hcn : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg _
    exact ⟨by positivity, div_le_self hcn (by norm_num)⟩
  · have hm : (caps.map (fun (c : Nat) => (c : ℝ))).map (· / 2) =
        caps.map (fun (c : Nat) => (c : ℝ) / 2) := List.map_map
    rw [← hm, real_sum_div, sum_natural_cast_real, h, Nat.cast_mul]
    ring

theorem unsplitRealSliceDilation (q : Nat) :
    realCoordinateSlice (dilatedCaps unsplitCaps q) (q * 6) =
      (fun xs : List ℝ => xs.map ((q : ℝ) * ·)) '' realCoordinateSlice unsplitCaps 6 :=
  realSliceDilation unsplitCaps 6 q (realSliceNonempty_of_double_sum _ _ (by decide))

theorem splitRealSliceDilation (q : Nat) :
    realCoordinateSlice (dilatedCaps splitCaps q) (q * 6) =
      (fun xs : List ℝ => xs.map ((q : ℝ) * ·)) '' realCoordinateSlice splitCaps 6 :=
  realSliceDilation splitCaps 6 q (realSliceNonempty_of_double_sum _ _ (by decide))

/-- Integer vectors in the geometric dilation have exactly the declared membership. -/
theorem integerPoint_iff_in_dilation (caps : List Nat) (total q : Nat)
    (hne : (realCoordinateSlice caps total).Nonempty) (v : List Int) :
    v ∈ integerCoordinateSlice (dilatedCaps caps q) (q * total) ↔
      v.map (fun (a : Int) => (a : ℝ)) ∈
        (fun xs : List ℝ => xs.map ((q : ℝ) * ·)) '' realCoordinateSlice caps total := by
  rw [← realSliceDilation caps total q hne]
  exact integerCoordinateSlice_iff_real _ _ _

/-- Exact standalone noninterlacing for the numerator coefficient vectors
formed from cardinalities of the two dilated integer point sets. -/
theorem integerPointNumeratorsDoNotInterlace :
    ¬ ∃ ps qs : List ℝ,
      (∀ x : ℝ, x ∈ ps ↔
        evalAsc (ehrhartNumerator 10 (fun q => (integerPointCount unsplitCaps 6 q : Int))) x = 0) ∧
      (∀ x : ℝ, x ∈ qs ↔
        evalAsc (ehrhartNumerator 11 (fun q => (integerPointCount splitCaps 6 q : Int))) x = 0) ∧
      alternatingRoots ps qs := by
  rw [unsplitIntegerCounts, splitIntegerCounts]
  exact compositionRowsDoNotInterlace

private theorem foldl_factorial (k : Nat) :
    (List.range k).foldl (fun acc i => acc * (i + 1)) 1 = k.factorial := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      Nat.factorial_succ, Nat.mul_comm]

private theorem foldl_descFactorial (m k : Nat) :
    (List.range k).foldl (fun acc i => acc * (m - i)) 1 = m.descFactorial k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      Nat.descFactorial_succ, Nat.mul_comm]

private theorem binom_eq_choose (m k : Nat) : binom m k = m.choose k := by
  unfold binom
  split
  · exact (Nat.choose_eq_zero_of_lt ‹m < k›).symm
  · rw [foldl_factorial, foldl_descFactorial, Nat.choose_eq_descFactorial_div_factorial]

private theorem alternating_eq_neg_one_pow (n : Nat) : alternating n = (-1 : Int) ^ n := by
  simp [alternating, neg_one_pow_eq_ite, Nat.even_iff]

private theorem list_sum_range (f : Nat → Int) (n : Nat) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, List.sum_append, ih, Finset.sum_range_succ]

private theorem coeff_one_sub_X_pow (m j : Nat) :
    PowerSeries.coeff Int j ((1 - PowerSeries.X : PowerSeries Int) ^ m) =
      (-1 : Int) ^ j * (m.choose j : Int) := by
  have hneg : (1 : PowerSeries Int) - PowerSeries.X =
      PowerSeries.C Int (-1) * PowerSeries.X + 1 := by simp [sub_eq_add_neg, add_comm]
  rw [hneg, add_pow, map_sum]
  have hterm (i : Nat) :
      PowerSeries.coeff Int j
        ((PowerSeries.C Int (-1) * PowerSeries.X) ^ i *
          (1 : PowerSeries Int) ^ (m - i) * (m.choose i : PowerSeries Int)) =
      if j = i then (-1 : Int) ^ i * (m.choose i : Int) else 0 := by
    have heq :
        (PowerSeries.C Int (-1) * PowerSeries.X) ^ i *
          (1 : PowerSeries Int) ^ (m - i) * (m.choose i : PowerSeries Int) =
        PowerSeries.C Int ((-1 : Int) ^ i * (m.choose i : Int)) * PowerSeries.X ^ i := by
      simp only [one_pow, mul_one, mul_pow, map_mul, map_pow, map_natCast]
      ac_rfl
    rw [heq, PowerSeries.coeff_C_mul_X_pow]
  simp_rw [hterm]
  by_cases hj : j < m + 1
  · rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Ne.symm hij]
    · intro hh
      exact (hh (Finset.mem_range.mpr hj)).elim
  · have hj' : m < j := by omega
    rw [Nat.choose_eq_zero_of_lt hj']
    simp only [Nat.cast_zero, mul_zero]
    apply Finset.sum_eq_zero
    intro i hi
    have hij : j ≠ i := by have := Finset.mem_range.mp hi; omega
    simp [hij]

/-- The count series multiplied by the denominator factor for dimension d. -/
noncomputable def normalizedCountSeries (d : Nat) (count : Nat → Int) : PowerSeries Int :=
  (1 - PowerSeries.X) ^ (d + 1) * PowerSeries.mk count

/-- The finite vector records the first d+1 coefficients of the normalized count series. -/
theorem ehrhartNumerator_eq_series_prefix (d : Nat) (count : Nat → Int) :
    ehrhartNumerator d count =
      (List.range (d + 1)).map (fun j => PowerSeries.coeff Int j
        (normalizedCountSeries d count)) := by
  unfold ehrhartNumerator
  apply List.map_congr_left
  intro k _
  rw [normalizedCountSeries, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_one_sub_X_pow, PowerSeries.coeff_mk, binom_eq_choose,
    alternating_eq_neg_one_pow, Int.ofNat_eq_coe, list_sum_range]

/-- If a polynomial represents the normalized series, its coefficients through the chosen
dimension are exactly the certified finite vector. -/
theorem ehrhartNumerator_of_seriesPolynomial (d : Nat) (count : Nat → Int)
    (p : Polynomial Int) (hp : (p : PowerSeries Int) = normalizedCountSeries d count) :
    ehrhartNumerator d count = (List.range (d + 1)).map p.coeff := by
  rw [ehrhartNumerator_eq_series_prefix, ← hp]
  simp

private theorem evalAsc_append_single (cs : List Int) (c : Int) (x : ℝ) :
    evalAsc (cs ++ [c]) x = evalAsc cs x + (c : ℝ) * x ^ cs.length := by
  induction cs with
  | nil => simp [evalAsc]
  | cons a cs ih =>
    simp only [List.cons_append, evalAsc, ih, List.length_cons, pow_succ]
    ring

private theorem evalAsc_range (f : Nat → Int) (n : Nat) (x : ℝ) :
    evalAsc ((List.range n).map f) x = ∑ j ∈ Finset.range n, (f j : ℝ) * x ^ j := by
  induction n with
  | zero => simp [evalAsc]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, evalAsc_append_single,
      Finset.sum_range_succ, ih]
    simp

theorem evalAsc_of_seriesPolynomial (d : Nat) (count : Nat → Int)
    (p : Polynomial Int) (hp : (p : PowerSeries Int) = normalizedCountSeries d count)
    (hdegree : p.natDegree ≤ d) (x : ℝ) :
    evalAsc (ehrhartNumerator d count) x = p.eval₂ (Int.castRingHom ℝ) x := by
  rw [ehrhartNumerator_of_seriesPolynomial _ _ _ hp, evalAsc_range,
    Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hdegree) x]
  rfl

/-- The normalized count-series polynomials cannot have weakly alternating lists
of their complete real roots, provided they have the stated degree bounds. -/
theorem integerPointSeriesPolynomialsDoNotInterlace (p q : Polynomial Int)
    (hp : (p : PowerSeries Int) =
      normalizedCountSeries 10 (fun i => (integerPointCount unsplitCaps 6 i : Int)))
    (hq : (q : PowerSeries Int) =
      normalizedCountSeries 11 (fun i => (integerPointCount splitCaps 6 i : Int)))
    (hdp : p.natDegree ≤ 10) (hdq : q.natDegree ≤ 11) :
    ¬ ∃ ps qs : List ℝ,
      (∀ x : ℝ, x ∈ ps ↔ p.eval₂ (Int.castRingHom ℝ) x = 0) ∧
      (∀ x : ℝ, x ∈ qs ↔ q.eval₂ (Int.castRingHom ℝ) x = 0) ∧
      alternatingRoots ps qs := by
  rintro ⟨ps, qs, hps, hqs, halt⟩
  exact integerPointNumeratorsDoNotInterlace ⟨ps, qs,
    fun x => (hps x).trans (by rw [evalAsc_of_seriesPolynomial _ _ _ hp hdp x]),
    fun x => (hqs x).trans (by rw [evalAsc_of_seriesPolynomial _ _ _ hq hdq x]), halt⟩

#print axioms integerCoordinateSlice_iff_real
#print axioms integerPointEquiv
#print axioms cardinality_eq_boundedCount
#print axioms integerPoint_iff_in_dilation
#print axioms unsplitRealSliceDilation
#print axioms splitRealSliceDilation
#print axioms integerPointNumeratorsDoNotInterlace
#print axioms ehrhartNumerator_eq_series_prefix
#print axioms ehrhartNumerator_of_seriesPolynomial
#print axioms integerPointSeriesPolynomialsDoNotInterlace

end PrismSplit
