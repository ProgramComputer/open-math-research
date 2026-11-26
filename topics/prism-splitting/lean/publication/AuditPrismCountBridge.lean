import AuditReferenceSpecs
import AuditPrismExportType

namespace AuditReference

open PrismSplit Polynomial

private abbrev Admissible (c : List ℕ) (k m : ℕ)
    (x : Fin c.length → Fin (m * k + 1)) : Prop :=
  (∀ i : Fin c.length, (x i).val ≤ m * c.get i) ∧
    ∑ i : Fin c.length, (x i).val = m * k

private theorem ofFn_forall₂ {c : List ℕ} (m : ℕ) (x : Fin c.length → ℕ) :
    List.Forall₂ (· ≤ ·) (List.ofFn x) (dilatedCaps c m) ↔
      ∀ i : Fin c.length, x i ≤ m * c.get i := by
  rw [dilatedCaps, List.forall₂_map_right_iff, List.forall₂_iff_get]
  constructor
  · intro h i
    have hi := h.2 i.val (by simpa using i.isLt) i.isLt
    simpa [List.get_ofFn] using hi
  · intro h
    refine ⟨List.length_ofFn, ?_⟩
    intro i hi hj
    simpa [List.get_ofFn] using h ⟨i, hj⟩

private noncomputable def admissibleEquiv (c : List ℕ) (k m : ℕ) :
    {x : Fin c.length → Fin (m*k+1) // Admissible c k m x} ≃
      {v : List ℕ // v ∈ boundedCompositions (dilatedCaps c m) (m*k)} := by
  let toList (x : {x : Fin c.length → Fin (m*k+1) // Admissible c k m x}) :
      {v : List ℕ // v ∈ boundedCompositions (dilatedCaps c m) (m*k)} :=
    ⟨List.ofFn (fun i => (x.val i).val), mem_boundedCompositions.mpr
      ⟨(ofFn_forall₂ _ _).mpr x.property.1, List.sum_ofFn.trans x.property.2⟩⟩
  refine Equiv.ofBijective toList ⟨?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact congrFun (List.ofFn_injective (congrArg Subtype.val h)) i
  · intro l
    obtain ⟨hb, hs⟩ := mem_boundedCompositions.mp l.property
    have hl : l.val.length = c.length := hb.length_eq.trans (List.length_map _)
    let w (i : Fin c.length) : ℕ := l.val.get (Fin.cast hl.symm i)
    have hw : List.ofFn w = l.val := by
      simpa only [w, List.ofFn_get] using (List.ofFn_congr hl l.val.get).symm
    have hsum : ∑ i, w i = m*k := by rw [← List.sum_ofFn, hw, hs]
    let x (i : Fin c.length) : Fin (m*k+1) :=
      ⟨w i, Nat.lt_succ_of_le ((Finset.single_le_sum (f := w) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans (le_of_eq hsum))⟩
    have hx : Admissible c k m x := by
      refine ⟨(ofFn_forall₂ m w).mp (hw.symm ▸ hb), hsum⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hw⟩

/-- The independently enumerated bounded tuples count the geometric dilation. -/
theorem prismCount_eq_integerPointCount (c : List ℕ) (k m : ℕ) :
    prismCount c k m = integerPointCount c k m := by
  classical
  let e := (admissibleEquiv c k m).trans (integerPointEquiv (dilatedCaps c m) (m*k)).symm
  have hh := Fintype.card_congr e
  rw [Fintype.card_subtype] at hh
  exact hh

private theorem one_sub_coeff (n i : ℕ) :
    PowerSeries.coeff (R := Int) i ((1 - PowerSeries.X : PowerSeries Int) ^ n) =
      (-1 : Int)^i * (n.choose i : Int) := by
  have he := one_sub_X_pow_expansion 1 n
  simp only [pow_one, one_mul] at he
  rw [he, map_sum]
  simp only [PowerSeries.coeff_C_mul_X_pow]
  by_cases hi : i ≤ n
  · rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hne
      simp [Ne.symm hne]
    · intro h
      exact (h (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))).elim
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hi), Nat.cast_zero, mul_zero]
    apply Finset.sum_eq_zero
    intro j hj
    have hij : i ≠ j := by
      have := Finset.mem_range.mp hj
      omega
    simp [hij]

/-- An equality of the actual normalized count series implies the coefficient
    identity in the source for every degree, including the vanishing tail. -/
theorem isPrismNumerator_of_slice {n k : ℕ} {caps : Fin n → ℕ}
    {hne : (realFinSlice caps k).Nonempty} {p : Polynomial Int}
    (hd : Module.finrank ℝ (affineSpan ℝ (realFinSlice caps k)).direction + 1 =
      (List.ofFn caps).length)
    (hp : (p : PowerSeries Int) = AuditExportType.sliceNumerator caps k hne) :
    IsPrismNumerator (List.ofFn caps) k (p.map (Int.castRingHom ℝ)) := by
  intro j
  rw [AuditExportType.sliceNumerator, hd] at hp
  have h := congrArg (PowerSeries.coeff (R := Int) j) hp
  rw [Polynomial.coeff_coe, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [one_sub_coeff, PowerSeries.coeff_mk, finLatticeCount_eq,
    ← prismCount_eq_integerPointCount] at h
  rw [Polynomial.coeff_map]
  change ((p.coeff j : Int) : ℝ) = _
  rw [h]
  push_cast <;> rfl

#print axioms prismCount_eq_integerPointCount
#print axioms isPrismNumerator_of_slice

end AuditReference
