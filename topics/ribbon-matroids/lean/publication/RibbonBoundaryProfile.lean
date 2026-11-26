import RibbonNarayanaSpec

/-!
# The boundary words of nonempty connected ribbons

The two north-prefix counts describe the cells along each anti-diagonal.
The no-square condition bounds their gap by one. A circuit crossing an
interior cut excludes equality of the counts there, by basis exchange.
-/

namespace Ribbon.Source

private theorem card_prefix_succ {n t : ℕ} (P : Fin n → Prop) [DecidablePred P] (ht : t < n) :
    ((Finset.univ : Finset (Fin n)).filter fun i => i.val < t + 1 ∧ P i).card =
      ((Finset.univ : Finset (Fin n)).filter fun i => i.val < t ∧ P i).card +
        (if P ⟨t, ht⟩ then 1 else 0) := by
  classical
  let j : Fin n := ⟨t, ht⟩
  by_cases hp : P j
  · have he : (Finset.univ.filter fun i : Fin n => i.val < t + 1 ∧ P i) =
        insert j (Finset.univ.filter fun i : Fin n => i.val < t ∧ P i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨hi, hpi⟩
        by_cases hij : i.val = t
        · exact Or.inl (Fin.ext hij)
        · exact Or.inr ⟨by omega, hpi⟩
      · rintro (rfl | ⟨hi, hpi⟩)
        · exact ⟨by show t < t + 1; omega, hp⟩
        · exact ⟨by omega, hpi⟩
    rw [he, Finset.card_insert_of_notMem, if_pos hp]
    simp [j]
  · have he : (Finset.univ.filter fun i : Fin n => i.val < t + 1 ∧ P i) =
        (Finset.univ.filter fun i : Fin n => i.val < t ∧ P i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hi, hpi⟩
        have hij : i.val ≠ t := fun hv => hp ((Fin.ext hv : i = j) ▸ hpi)
        exact ⟨by omega, hpi⟩
      · exact fun h => ⟨by omega, h.2⟩
    rw [he, if_neg hp, Nat.add_zero]

@[simp] theorem prefixNorth_zero {n : ℕ} (p : Path n) : prefixNorth p 0 = 0 := by
  simp [prefixNorth]

theorem prefixNorth_succ {n t : ℕ} (p : Path n) (ht : t < n) :
    prefixNorth p (t + 1) = prefixNorth p t + if p ⟨t, ht⟩ = true then 1 else 0 :=
  card_prefix_succ (fun i => p i = true) ht

theorem prefixNorth_mono {n : ℕ} (p : Path n) : Monotone (prefixNorth p) := by
  intro a b hab
  unfold prefixNorth
  apply Finset.card_le_card
  intro i hi
  have he := (Finset.mem_filter.mp hi).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.1.trans_le hab, he.2⟩

theorem prefixNorth_le {n t : ℕ} (p : Path n) (ht : t ≤ n) : prefixNorth p t ≤ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [prefixNorth_succ p (by omega)]
    have h := ih (by omega)
    split_ifs <;> omega

theorem prefixNorth_le_succ {n t : ℕ} (p : Path n) (ht : t < n) :
    prefixNorth p (t + 1) ≤ prefixNorth p t + 1 := by
  rw [prefixNorth_succ p ht]
  split_ifs <;> omega

private def prefixEast {n : ℕ} (p : Path n) (t : ℕ) : ℕ := t - prefixNorth p t

private theorem prefixEast_succ {n t : ℕ} (p : Path n) (ht : t < n) :
    prefixEast p (t + 1) = prefixEast p t + if p ⟨t, ht⟩ = false then 1 else 0 := by
  unfold prefixEast
  rw [prefixNorth_succ p ht]
  have hb := prefixNorth_le p ht.le
  have hComplement : (if p ⟨t, ht⟩ = true then 1 else 0) +
      (if p ⟨t, ht⟩ = false then 1 else 0) = 1 := by
    cases h : p ⟨t, ht⟩ <;> simp [h]
  omega

private theorem prefixEast_mono_upto {n : ℕ} (p : Path n) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ n) :
    prefixEast p a ≤ prefixEast p b := by
  induction b with
  | zero =>
    have he : a = 0 := by omega
    rw [he]
  | succ b ih =>
    by_cases he : a = b + 1
    · rw [he]
    · have hh := ih (by omega) (by omega)
      rw [prefixEast_succ p (by omega)]
      exact hh.trans (Nat.le_add_right _ _)

private theorem exists_eastLevel {n : ℕ} (p : Path n) (x : ℕ) (hx : x < prefixEast p n) :
    ∃ y, eastLevel p x y := by
  have hExists : ∃ t, x < prefixEast p t := ⟨n, hx⟩
  let b := Nat.find hExists
  have hB : x < prefixEast p b := Nat.find_spec hExists
  have hLe : b ≤ n := Nat.find_min' hExists hx
  have hBPos : 0 < b := by
    by_contra! hz
    have he : b = 0 := by omega
    rw [he] at hB
    simp [prefixEast] at hB
  let t := b - 1
  have ht : t < n := by dsimp [t]; omega
  have hEq : t + 1 = b := by dsimp [t]; omega
  have htMin : prefixEast p t ≤ x := by
    exact le_of_not_gt (Nat.find_min hExists (by dsimp [t]; omega))
  rw [← hEq, prefixEast_succ p ht] at hB
  have hStep : p ⟨t, ht⟩ = false := by
    by_contra h
    rw [if_neg h, Nat.add_zero] at hB
    omega
  rw [if_pos hStep] at hB
  have hPrev : prefixEast p t = x := by omega
  have hNorth := prefixNorth_le p ht.le
  refine ⟨prefixNorth p t, ⟨⟨t, ht⟩, hStep, rfl, ?_⟩⟩
  unfold prefixEast at hPrev
  dsimp
  omega

private theorem eastLevel_iff_prefix_bound {n x b y : ℕ} {p : Path n}
    (h : eastLevel p x b) (ht : x + y + 1 ≤ n) : b ≤ y ↔ prefixNorth p (x + y + 1) ≤ y := by
  obtain ⟨i, hStep, hNorth, hIdx⟩ := h
  have hi : prefixEast p i.val = x := by unfold prefixEast; omega
  have hiSucc : prefixEast p (i.val + 1) = x + 1 := by
    rw [prefixEast_succ p i.isLt, hi, if_pos hStep]
  constructor
  · intro hby
    have htE := prefixEast_mono_upto p (a := i.val + 1) (b := x + y + 1) (by omega) ht
    rw [hiSucc] at htE
    unfold prefixEast at htE
    omega
  · intro hp
    by_contra! hby
    have htE := prefixEast_mono_upto p (a := x + y + 1) (b := i.val) (by omega) i.isLt.le
    rw [hi] at htE
    unfold prefixEast at htE
    omega

/-- A cell lies between the two north-prefix bounds on its anti-diagonal. -/
theorem cell_iff_prefix_counts {n r x y : ℕ} {M : Matroid (Fin n)} {lower upper : Path n}
    (h : IsRibbonPresentation M r lower upper) (ht : x + y + 1 ≤ n) :
    cell lower upper x y ↔ prefixNorth lower (x + y + 1) ≤ y ∧ y < prefixNorth upper (x + y + 1) := by
  constructor
  · rintro ⟨l, u, hl, hu, hly, hyu⟩
    exact ⟨(eastLevel_iff_prefix_bound hl ht).mp hly,
      lt_of_not_ge (fun h' => not_le_of_gt hyu ((eastLevel_iff_prefix_bound hu ht).mpr h'))⟩
  · rintro ⟨hLo, hHi⟩
    have hL : x < prefixEast lower (x + y + 1) := by unfold prefixEast; omega
    have hxL := hL.trans_le (prefixEast_mono_upto lower ht le_rfl)
    have hxU : x < prefixEast upper n := by
      simpa [prefixEast, h.endpoint_lower, h.endpoint_upper] using hxL
    obtain ⟨l, hl⟩ := exists_eastLevel lower x hxL
    obtain ⟨u, hu⟩ := exists_eastLevel upper x hxU
    exact ⟨l, u, hl, hu, (eastLevel_iff_prefix_bound hl ht).mpr hLo,
      lt_of_not_ge (fun h' => not_le_of_gt hHi ((eastLevel_iff_prefix_bound hu ht).mp h'))⟩

/-- Without a two-by-two block, the north-prefix gap is at most one at every time. -/
theorem IsRibbonPresentation.prefix_gap_le_one {n r : ℕ} {M : Matroid (Fin n)} {lower upper : Path n}
    (h : IsRibbonPresentation M r lower upper) {t : ℕ} (ht : t ≤ n) :
    prefixNorth upper t ≤ prefixNorth lower t + 1 := by
  by_contra! hGap
  let y := prefixNorth lower t
  let x := t - y - 2
  have hU := prefixNorth_le upper ht
  have htPos : 0 < t := by omega
  have htLt : t < n := by
    by_contra! hh
    have he : t = n := by omega
    rw [he, h.endpoint_upper, h.endpoint_lower] at hGap
    omega
  have hEq : t = x + y + 2 := by dsimp [x, y]; omega
  have hLp := prefixNorth_mono lower (a := t - 1) (b := t) (by omega)
  have hUp := prefixNorth_le_succ upper (t := t - 1) (by omega)
  have hLn := prefixNorth_le_succ lower htLt
  have hUn := prefixNorth_mono upper (a := t) (b := t + 1) (by omega)
  have hp : t - 1 + 1 = t := by omega
  rw [hp] at hUp
  apply h.no_square x y
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (cell_iff_prefix_counts h (by omega)).mpr
    have he : x + y + 1 = t - 1 := by omega
    rw [he]
    exact ⟨hLp, by dsimp [y]; omega⟩
  · apply (cell_iff_prefix_counts h (by omega)).mpr
    have he : (x + 1) + y + 1 = t := by omega
    rw [he]
    exact ⟨by rfl, by dsimp [y]; omega⟩
  · apply (cell_iff_prefix_counts h (by omega)).mpr
    have he : x + (y + 1) + 1 = t := by omega
    rw [he]
    exact ⟨by dsimp [y]; omega, by dsimp [y]; omega⟩
  · apply (cell_iff_prefix_counts h (by omega)).mpr
    have he : (x + 1) + (y + 1) + 1 = t + 1 := by omega
    rw [he]
    exact ⟨hLn, by dsimp [y]; omega⟩

private theorem prefixBase_swap {n t : ℕ} (B : Set (Fin n)) {e f : Fin n}
    (he : e.val < t) (hf : t ≤ f.val) (heB : e ∉ B) :
    prefixBase (insert e B \ {f}) t = prefixBase B t + 1 := by
  classical
  let old := (Finset.univ : Finset (Fin n)).filter (fun i => i.val < t ∧ i ∈ B)
  have hOld : prefixBase B t = old.card := rfl
  have hEq : prefixBase (insert e B \ {f}) t = (insert e old).card := by
    unfold prefixBase old
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Set.mem_sdiff,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hi, (rfl | hiB), _⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hi, hiB⟩
    · intro hi
      have ht : i.val < t := hi.elim (fun h => h.symm ▸ he) And.left
      exact ⟨ht, hi.imp_right And.right, fun h => by rw [h] at ht; omega⟩
  rw [hEq, hOld, Finset.card_insert_of_notMem]
  simp [old, heB]

/-- If the boundary paths met at an interior time, every basis would have the same size
on its left. A circuit across that cut supplies a basis exchange that changes this size. -/
theorem IsRibbonPresentation.prefix_gap_pos {n r : ℕ} {M : Matroid (Fin n)} {lower upper : Path n}
    (h : IsRibbonPresentation M r lower upper) {t : ℕ} (ht₀ : 0 < t) (ht : t < n) :
    prefixNorth lower t < prefixNorth upper t := by
  let e : Fin n := ⟨0, ht₀.trans ht⟩
  let f : Fin n := ⟨t, ht⟩
  have hef : e ≠ f := fun heq => (Nat.ne_of_gt ht₀) (congrArg Fin.val heq).symm
  obtain ⟨C, hC, heC, hfC⟩ := h.connected e f hef
  obtain ⟨B, hB, hCB⟩ := (hC.sdiff_singleton_indep heC).exists_isBase_superset
  have heB : e ∉ B := by
    intro hmem
    apply hC.not_indep
    apply hB.indep.subset
    intro x hx
    by_cases hxe : x = e
    · exact hxe.symm ▸ hmem
    · exact hCB ⟨hx, by simpa using hxe⟩
  have hfB : f ∈ B := hCB ⟨hfC, by simpa using hef.symm⟩
  have hCIns : C ⊆ insert e B := by
    intro x hx
    by_cases hxe : x = e
    · exact Set.mem_insert_iff.mpr (Or.inl hxe)
    · exact Set.mem_insert_iff.mpr (Or.inr (hCB ⟨hx, by simpa using hxe⟩))
  have hfFund : f ∈ M.fundCircuit e B := (hC.eq_fundCircuit_of_subset hB.indep hCIns) ▸ hfC
  have heCl : e ∈ M.closure B := by
    rw [hB.closure_eq]
    exact hC.subset_ground heC
  have hSwapIndep := (hB.indep.mem_fundCircuit_iff heCl heB).mp hfFund
  have hSwap := hB.exchange_isBase_of_indep' hfB heB hSwapIndep
  have hCounts := (h.bases B).mp hB t ht.le
  have hNew := (h.bases (insert e B \ {f})).mp hSwap t ht.le
  rw [prefixBase_swap B (e := e) (f := f) (by exact ht₀) (by rfl) heB] at hNew
  omega

/-- The prefix gap for a connected ribbon is exactly one at every interior time. -/
theorem IsRibbonPresentation.prefix_gap_eq_one {n r : ℕ} {M : Matroid (Fin n)} {lower upper : Path n}
    (h : IsRibbonPresentation M r lower upper) {t : ℕ} (ht₀ : 0 < t) (ht : t < n) :
    prefixNorth upper t = prefixNorth lower t + 1 := by
  have hPos := h.prefix_gap_pos ht₀ ht
  have hLe := h.prefix_gap_le_one ht.le
  omega

theorem IsRibbonPresentation.length_ge_two {n r : ℕ} {M : Matroid (Fin n)} {lower upper : Path n}
    (h : IsRibbonPresentation M r lower upper) : 2 ≤ n := by
  obtain ⟨x, y, l, u, hl, hu, hly, hyu⟩ := h.nonempty
  obtain ⟨i, _, _, hi⟩ := hu
  have hlt := i.isLt
  omega

/-- The paths take the same step between the two extreme positions. -/
theorem IsRibbonPresentation.inner_step_eq {n r : ℕ} {M : Matroid (Fin n)} {lower upper : Path n}
    (h : IsRibbonPresentation M r lower upper) (i : Fin n) (h₀ : 0 < i.val) (hn : i.val + 1 < n) :
    lower i = upper i := by
  have hBefore := h.prefix_gap_eq_one h₀ i.isLt
  have hAfter := h.prefix_gap_eq_one (t := i.val + 1) (by omega) hn
  rw [prefixNorth_succ lower i.isLt, prefixNorth_succ upper i.isLt] at hAfter
  cases hl : lower i <;> cases hu : upper i <;> simp [hl, hu] at hAfter ⊢ <;> omega

theorem IsRibbonPresentation.first_steps {n r : ℕ} {M : Matroid (Fin n)} {lower upper : Path n}
    (h : IsRibbonPresentation M r lower upper) (hn : 0 < n) :
    lower ⟨0, hn⟩ = false ∧ upper ⟨0, hn⟩ = true := by
  have hLen := h.length_ge_two
  have he := h.prefix_gap_eq_one (t := 1) (by omega) (by omega)
  rw [show 1 = 0 + 1 from rfl, prefixNorth_succ lower hn, prefixNorth_succ upper hn] at he
  simp only [prefixNorth_zero, Nat.zero_add] at he
  cases hl : lower ⟨0, hn⟩ <;> cases hu : upper ⟨0, hn⟩ <;> simp [hl, hu] at he ⊢

theorem IsRibbonPresentation.last_steps {n r : ℕ} {M : Matroid (Fin n)} {lower upper : Path n}
    (h : IsRibbonPresentation M r lower upper) (hn : 0 < n) :
    lower ⟨n - 1, by omega⟩ = true ∧ upper ⟨n - 1, by omega⟩ = false := by
  have hLen := h.length_ge_two
  have hi : n - 1 < n := by omega
  have hLast : n - 1 + 1 = n := by omega
  have he := h.prefix_gap_eq_one (t := n - 1) (by omega) hi
  have hl := prefixNorth_succ lower hi
  have hu := prefixNorth_succ upper hi
  rw [hLast, h.endpoint_lower] at hl
  rw [hLast, h.endpoint_upper] at hu
  cases hL : lower ⟨n - 1, hi⟩ <;> cases hU : upper ⟨n - 1, hi⟩ <;>
    simp [hL, hU] at hl hu ⊢ <;> omega

#print axioms cell_iff_prefix_counts
#print axioms IsRibbonPresentation.prefix_gap_le_one
#print axioms IsRibbonPresentation.prefix_gap_pos
#print axioms IsRibbonPresentation.prefix_gap_eq_one
#print axioms IsRibbonPresentation.inner_step_eq
#print axioms IsRibbonPresentation.first_steps
#print axioms IsRibbonPresentation.last_steps

end Ribbon.Source
