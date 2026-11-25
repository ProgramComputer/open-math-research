import PrismSeriesClosure
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith

/-!
Affine dimensions of the two box slices and their identification with
the ordered-coordinate models used in the lattice-count certificates.
-/

namespace PrismSplit

open scoped BigOperators Pointwise

/-- The Ferroni–McGinnis box slice in the standard finite-coordinate model. -/
def realFinSlice {n : Nat} (caps : Fin n → Nat) (total : Nat) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i ∧ x i ≤ (caps i : ℝ)) ∧ ∑ i, x i = (total : ℝ)}

theorem realFinSlice_eq_box_intersection {n : Nat} (caps : Fin n → Nat) (total : Nat) :
    realFinSlice caps total =
      Set.Icc (0 : Fin n → ℝ) (fun i => (caps i : ℝ)) ∩
        {x | ∑ i, x i = (total : ℝ)} := by
  ext x
  change ((∀ i, 0 ≤ x i ∧ x i ≤ (caps i : ℝ)) ∧ ∑ i, x i = (total : ℝ)) ↔
      (((∀ i, 0 ≤ x i) ∧ ∀ i, x i ≤ (caps i : ℝ)) ∧ ∑ i, x i = (total : ℝ))
  constructor
  · rintro ⟨h, hs⟩
    exact ⟨⟨fun i => (h i).1, fun i => (h i).2⟩, hs⟩
  · rintro ⟨⟨hl, hu⟩, hs⟩
    exact ⟨fun i => ⟨hl i, hu i⟩, hs⟩

private theorem forall₂_ofFn_iff {α β : Type*} {n : Nat}
    (r : α → β → Prop) (f : Fin n → α) (g : Fin n → β) :
    List.Forall₂ r (List.ofFn f) (List.ofFn g) ↔ ∀ i, r (f i) (g i) := by
  constructor
  · intro h i
    have hp := h.get (i := i.val) (by simp) (by simp)
    simpa [List.get_ofFn] using hp
  · intro h
    apply List.forall₂_of_length_eq_of_get (by simp)
    intro i hi _
    have hn : i < n := by simpa using hi
    simpa [List.get_ofFn] using h ⟨i, hn⟩

theorem realFinSlice_iff_ofFn {n : Nat} (caps : Fin n → Nat) (total : Nat) (x : Fin n → ℝ) :
    x ∈ realFinSlice caps total ↔ List.ofFn x ∈ realCoordinateSlice (List.ofFn caps) total := by
  change ((∀ i, 0 ≤ x i ∧ x i ≤ (caps i : ℝ)) ∧ ∑ i, x i = (total : ℝ)) ↔
      (List.Forall₂ (fun (a : ℝ) (c : Nat) => 0 ≤ a ∧ a ≤ (c : ℝ))
        (List.ofFn x) (List.ofFn caps) ∧ (List.ofFn x).sum = (total : ℝ))
  rw [forall₂_ofFn_iff, List.sum_ofFn]

private theorem exists_ofFn_eq {α : Type*} {n : Nat} (l : List α) (hl : l.length = n) :
    ∃ f : Fin n → α, List.ofFn f = l :=
  ⟨fun i => l.get (Fin.cast hl.symm i),
    by simpa only [List.ofFn_get] using (List.ofFn_congr hl l.get).symm⟩

theorem ofFn_image_realFinSlice {n : Nat} (caps : Fin n → Nat) (total : Nat) :
    List.ofFn '' realFinSlice caps total = realCoordinateSlice (List.ofFn caps) total := by
  ext l
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (realFinSlice_iff_ofFn _ _ _).mp hx
  · intro hl
    have hlen : l.length = n := hl.1.length_eq.trans List.length_ofFn
    obtain ⟨x, hx⟩ := exists_ofFn_eq l hlen
    exact ⟨x, (realFinSlice_iff_ofFn _ _ _).mpr (hx ▸ hl), hx⟩

private def sumLinear (n : Nat) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i
  map_add' x y := Finset.sum_add_distrib
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]

private noncomputable def boxMidpoint {n : Nat} (caps : Fin n → Nat) (i : Fin n) : ℝ :=
  (caps i : ℝ) / 2

private theorem boxMidpoint_mem {n : Nat} (caps : Fin n → Nat) (total : Nat)
    (hsum : ∑ i, caps i = 2 * total) : boxMidpoint caps ∈ realFinSlice caps total := by
  refine ⟨fun i => ⟨div_nonneg (Nat.cast_nonneg _) (by norm_num),
    div_le_self (Nat.cast_nonneg _) (by norm_num)⟩, ?_⟩
  have hreal : (∑ i, (caps i : ℝ)) = 2 * (total : ℝ) := by exact_mod_cast hsum
  change (∑ i, (caps i : ℝ) / 2) = (total : ℝ)
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  rw [hreal]
  ring

private theorem vectorSpan_realFinSlice {n : Nat} (caps : Fin n → Nat) (total : Nat)
    (hpositive : ∀ i, 0 < caps i) (hsum : ∑ i, caps i = 2 * total) :
    vectorSpan ℝ (realFinSlice caps total) = LinearMap.ker (sumLinear n) := by
  apply le_antisymm
  · rw [vectorSpan_def, Submodule.span_le]
    intro v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_vsub.mp hv
    change x -ᵥ y ∈ LinearMap.ker (sumLinear n)
    rw [LinearMap.mem_ker, vsub_eq_sub, map_sub]
    exact sub_eq_zero.mpr (hx.2.trans hy.2.symm)
  · intro v hv
    let center := boxMidpoint caps
    have hc : center ∈ realFinSlice caps total := boxMidpoint_mem caps total hsum
    have hzero : ∑ i, v i = 0 := LinearMap.mem_ker.mp hv
    let bound : ℝ := ∑ i, |v i|
    have hbound : 0 ≤ bound := Finset.sum_nonneg fun i _ => abs_nonneg (v i)
    let eps : ℝ := 1 / (2 * (bound + 1))
    have heps : 0 < eps := by dsimp only [eps]; positivity
    let x : Fin n → ℝ := center + eps • v
    have hx : x ∈ realFinSlice caps total := by
      refine ⟨?_, ?_⟩
      · intro i
        have hvi : |v i| ≤ bound :=
          Finset.single_le_sum (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)
        have hperturb : |eps * v i| ≤ (1 : ℝ) / 2 := by
          rw [abs_mul, abs_of_pos heps]
          calc
            _ ≤ eps * (bound + 1) := mul_le_mul_of_nonneg_left (by linarith) heps.le
            _ = _ := by
              dsimp only [eps]
              have hne : bound + 1 ≠ 0 := by linarith
              field_simp
              ring
        have hci : (1 : ℝ) ≤ (caps i : ℝ) := by exact_mod_cast (hpositive i)
        rw [abs_le] at hperturb
        change 0 ≤ (caps i : ℝ) / 2 + eps * v i ∧
          (caps i : ℝ) / 2 + eps * v i ≤ (caps i : ℝ)
        exact ⟨by linarith [hperturb.1], by linarith [hperturb.2]⟩
      · change (∑ i, (center i + eps * v i)) = (total : ℝ)
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hzero, mul_zero, add_zero]
        exact hc.2
    have hdir := vsub_mem_vectorSpan ℝ hx hc
    have hdiff : x -ᵥ center = eps • v := by
      change center + eps • v - center = eps • v
      abel
    rw [hdiff] at hdir
    have hscaled := (vectorSpan ℝ (realFinSlice caps total)).smul_mem eps⁻¹ hdir
    rwa [smul_smul, inv_mul_cancel₀ heps.ne', one_smul] at hscaled

private theorem sumLinear_ker_finrank (n : Nat) :
    Module.finrank ℝ (LinearMap.ker (sumLinear (n + 1))) = n := by
  have hsurj : Function.Surjective (sumLinear (n + 1)) := by
    intro a
    refine ⟨Pi.single 0 a, ?_⟩
    change ∑ i : Fin (n + 1), Pi.single 0 a i = a
    exact Fintype.sum_pi_single' (0 : Fin (n + 1)) a
  have h := (sumLinear (n + 1)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top,
    Module.finrank_self, Module.finrank_pi, Fintype.card_fin] at h
  omega

theorem affineDimension_realFinSlice {n : Nat} (caps : Fin (n + 1) → Nat) (total : Nat)
    (hpositive : ∀ i, 0 < caps i) (hsum : ∑ i, caps i = 2 * total) :
    Module.finrank ℝ (affineSpan ℝ (realFinSlice caps total)).direction = n := by
  rw [direction_affineSpan, vectorSpan_realFinSlice caps total hpositive hsum]
  exact sumLinear_ker_finrank n

def unsplitFinCaps (i : Fin 11) : Nat := if i.val = 10 then 2 else 1

def splitFinCaps (_ : Fin 12) : Nat := 1

theorem unsplitFinCaps_list : List.ofFn unsplitFinCaps = unsplitCaps := by decide

theorem splitFinCaps_list : List.ofFn splitFinCaps = splitCaps := by decide

theorem unsplitAffineDimension :
    Module.finrank ℝ (affineSpan ℝ (realFinSlice unsplitFinCaps 6)).direction = 10 :=
  affineDimension_realFinSlice unsplitFinCaps 6 (by decide) (by decide)

theorem splitAffineDimension :
    Module.finrank ℝ (affineSpan ℝ (realFinSlice splitFinCaps 6)).direction = 11 :=
  affineDimension_realFinSlice splitFinCaps 6 (by decide) (by decide)


/-- Integer vectors whose real images lie in a geometric dilation of the box slice. -/
def integerFinDilation {n : Nat} (caps : Fin n → Nat) (total q : Nat) : Set (Fin n → Int) :=
  {v | (fun i => (v i : ℝ)) ∈ (fun x : Fin n → ℝ => (q : ℝ) • x) '' realFinSlice caps total}

theorem integerFinDilation_iff_ofFn {n : Nat} (caps : Fin n → Nat) (total q : Nat)
    (hne : (realFinSlice caps total).Nonempty) (v : Fin n → Int) :
    v ∈ integerFinDilation caps total q ↔
      List.ofFn v ∈ integerCoordinateSlice (dilatedCaps (List.ofFn caps) q) (q * total) := by
  have hlist : (realCoordinateSlice (List.ofFn caps) total).Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨List.ofFn p, (realFinSlice_iff_ofFn _ _ _).mp hp⟩
  rw [integerPoint_iff_in_dilation _ _ _ hlist]
  constructor
  · rintro ⟨p, hp, heq⟩
    refine ⟨List.ofFn p, (realFinSlice_iff_ofFn _ _ _).mp hp, ?_⟩
    change (List.ofFn p).map ((q : ℝ) * ·) = (List.ofFn v).map (fun a : Int => (a : ℝ))
    rw [List.map_ofFn, List.map_ofFn]
    apply congrArg List.ofFn
    exact heq
  · rintro ⟨l, hl, heq⟩
    have hlen : l.length = n := hl.1.length_eq.trans List.length_ofFn
    obtain ⟨p, hp⟩ := exists_ofFn_eq l hlen
    refine ⟨p, (realFinSlice_iff_ofFn _ _ _).mpr (hp ▸ hl), ?_⟩
    apply List.ofFn_injective
    change l.map ((q : ℝ) * ·) = (List.ofFn v).map (fun a : Int => (a : ℝ)) at heq
    rw [← hp, List.map_ofFn, List.map_ofFn] at heq
    exact heq

/-- Recording the coordinates in order gives a lattice-point bijection. -/
noncomputable def finLatticeEquiv {n : Nat} (caps : Fin n → Nat) (total q : Nat)
    (hne : (realFinSlice caps total).Nonempty) :
    integerFinDilation caps total q ≃
      integerCoordinateSlice (dilatedCaps (List.ofFn caps) q) (q * total) := by
  let toList (v : integerFinDilation caps total q) :
      integerCoordinateSlice (dilatedCaps (List.ofFn caps) q) (q * total) :=
    ⟨List.ofFn v.val, (integerFinDilation_iff_ofFn _ _ _ hne _).mp v.property⟩
  refine Equiv.ofBijective toList ⟨?_, ?_⟩
  · intro v w h
    exact Subtype.ext (List.ofFn_injective (congrArg Subtype.val h))
  · intro v
    have hlen : v.val.length = n := by
      have h := v.property.1.length_eq
      simpa [dilatedCaps] using h
    obtain ⟨w, hw⟩ := exists_ofFn_eq v.val hlen
    refine ⟨⟨w, (integerFinDilation_iff_ofFn _ _ _ hne _).mpr (hw ▸ v.property)⟩, ?_⟩
    exact Subtype.ext hw

noncomputable def finLatticeCount {n : Nat} (caps : Fin n → Nat) (total q : Nat)
    (hne : (realFinSlice caps total).Nonempty) : Nat :=
  letI := Fintype.ofEquiv _ (finLatticeEquiv caps total q hne).symm
  Fintype.card (integerFinDilation caps total q)

theorem finLatticeCount_eq {n : Nat} (caps : Fin n → Nat) (total q : Nat)
    (hne : (realFinSlice caps total).Nonempty) :
    finLatticeCount caps total q hne = integerPointCount (List.ofFn caps) total q := by
  letI := Fintype.ofEquiv _ (finLatticeEquiv caps total q hne).symm
  exact Fintype.card_congr (finLatticeEquiv caps total q hne)

theorem unsplitFinNonempty : (realFinSlice unsplitFinCaps 6).Nonempty :=
  ⟨boxMidpoint unsplitFinCaps, boxMidpoint_mem unsplitFinCaps 6 (by decide)⟩

theorem splitFinNonempty : (realFinSlice splitFinCaps 6).Nonempty :=
  ⟨boxMidpoint splitFinCaps, boxMidpoint_mem splitFinCaps 6 (by decide)⟩

theorem lastUnsplitBound : unsplitFinCaps (Fin.last 10) = 2 := by decide

theorem splitReplacesLastBound :
    List.ofFn splitFinCaps =
      (List.ofFn unsplitFinCaps).dropLast ++ [unsplitFinCaps (Fin.last 10) - 1, 1] := by decide

theorem unsplitFinEhrhartSeries :
    (unsplitEhrhartPolynomial : PowerSeries Int) =
      normalizedCountSeries
        (Module.finrank ℝ (affineSpan ℝ (realFinSlice unsplitFinCaps 6)).direction)
        (fun q => (finLatticeCount unsplitFinCaps 6 q unsplitFinNonempty : Int)) := by
  rw [unsplitAffineDimension]
  simpa only [finLatticeCount_eq, unsplitFinCaps_list] using unsplitEhrhartSeries

theorem splitFinEhrhartSeries :
    (splitEhrhartPolynomial : PowerSeries Int) =
      normalizedCountSeries
        (Module.finrank ℝ (affineSpan ℝ (realFinSlice splitFinCaps 6)).direction)
        (fun q => (finLatticeCount splitFinCaps 6 q splitFinNonempty : Int)) := by
  rw [splitAffineDimension]
  simpa only [finLatticeCount_eq, splitFinCaps_list] using splitEhrhartSeries

private theorem finitePowerSum_degree_le (d : Nat) (f : Nat → Int) :
    (∑ i ∈ Finset.range (d + 1), Polynomial.C (f i) * Polynomial.X ^ i).natDegree ≤ d := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  have hne : k ≠ i := by
    have := Finset.mem_range.mp hi
    omega
  rw [Polynomial.coeff_C_mul_X_pow, if_neg hne]

private theorem coefficients_get {p : Polynomial Int} {m : Nat} {cs : List Int}
    (hc : (List.range m).map p.coeff = cs) (i : Nat) (hi : i < m) :
    p.coeff i = (cs[i]?).getD 0 := by
  have h := congrArg (fun l : List Int => (l[i]?).getD 0) hc
  simpa only [List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some] using h

private theorem degree_from_upper {p : Polynomial Int} {d : Nat} (hbound : p.natDegree ≤ d + 1)
    (hzero : p.coeff (d + 1) = 0) (hnonzero : p.coeff d ≠ 0) : p.natDegree = d := by
  refine le_antisymm ?_ (Polynomial.le_natDegree_of_ne_zero hnonzero)
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  by_cases heq : k = d + 1
  · simpa only [heq] using hzero
  · apply Polynomial.coeff_eq_zero_of_natDegree_lt
    omega

theorem unsplitEhrhartDegree : unsplitEhrhartPolynomial.natDegree = 9 := by
  have hcoeffs : (List.range 11).map unsplitEhrhartPolynomial.coeff = unsplitCoefficients := by
    rw [← ehrhartNumerator_of_seriesPolynomial 10 _ _ unsplitEhrhartSeries, unsplitIntegerCounts]
    exact unsplitCompositionCertificate
  have hbound : unsplitEhrhartPolynomial.natDegree ≤ 10 := finitePowerSum_degree_le 10 _
  have hz : unsplitEhrhartPolynomial.coeff 10 = 0 := coefficients_get hcoeffs 10 (by decide)
  have hn : unsplitEhrhartPolynomial.coeff 9 = 1 := coefficients_get hcoeffs 9 (by decide)
  exact degree_from_upper hbound hz (by rw [hn]; decide)

theorem splitEhrhartDegree : splitEhrhartPolynomial.natDegree = 10 := by
  have hcoeffs : (List.range 12).map splitEhrhartPolynomial.coeff = splitCoefficients := by
    rw [← ehrhartNumerator_of_seriesPolynomial 11 _ _ splitEhrhartSeries, splitIntegerCounts]
    exact splitCompositionCertificate
  have hbound : splitEhrhartPolynomial.natDegree ≤ 11 := finitePowerSum_degree_le 11 _
  have hz : splitEhrhartPolynomial.coeff 11 = 0 := coefficients_get hcoeffs 11 (by decide)
  have hn : splitEhrhartPolynomial.coeff 10 = 1 := coefficients_get hcoeffs 10 (by decide)
  exact degree_from_upper hbound hz (by rw [hn]; decide)

/-- The normalized series of the actual finite-coordinate slices are polynomials and
their complete real-root lists cannot alternate. -/
theorem finBoxSplitCounterexample :
    ∃ p q : Polynomial Int,
      p.natDegree = 9 ∧ q.natDegree = 10 ∧
      (p : PowerSeries Int) = normalizedCountSeries
        (Module.finrank ℝ (affineSpan ℝ (realFinSlice unsplitFinCaps 6)).direction)
        (fun i => (finLatticeCount unsplitFinCaps 6 i unsplitFinNonempty : Int)) ∧
      (q : PowerSeries Int) = normalizedCountSeries
        (Module.finrank ℝ (affineSpan ℝ (realFinSlice splitFinCaps 6)).direction)
        (fun i => (finLatticeCount splitFinCaps 6 i splitFinNonempty : Int)) ∧
      ¬ ∃ ps qs : List ℝ,
        (∀ x : ℝ, x ∈ ps ↔ p.eval₂ (Int.castRingHom ℝ) x = 0) ∧
        (∀ x : ℝ, x ∈ qs ↔ q.eval₂ (Int.castRingHom ℝ) x = 0) ∧
        alternatingRoots ps qs :=
  ⟨unsplitEhrhartPolynomial, splitEhrhartPolynomial, unsplitEhrhartDegree, splitEhrhartDegree,
    unsplitFinEhrhartSeries, splitFinEhrhartSeries, ehrhartPolynomialsDoNotInterlace⟩

#print axioms realFinSlice_eq_box_intersection
#print axioms ofFn_image_realFinSlice
#print axioms unsplitAffineDimension
#print axioms splitAffineDimension
#print axioms finLatticeEquiv
#print axioms unsplitFinEhrhartSeries
#print axioms splitFinEhrhartSeries
#print axioms unsplitEhrhartDegree
#print axioms splitEhrhartDegree
#print axioms finBoxSplitCounterexample

end PrismSplit
