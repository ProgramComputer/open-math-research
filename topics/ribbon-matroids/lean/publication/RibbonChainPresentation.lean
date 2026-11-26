import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin
import RibbonBoundaryProfile

/-!
# The interval-transversal basis model of connected ribbons

The union of boundary north positions gives the separator chain. Sorting
any basis converts the prefix conditions into the two endpoint bounds
on each representative. The bounds also force any distinct choice of
representatives to be increasing.
-/

namespace Ribbon.Source

open Set Finset

private def countBelow {n r : ℕ} (f : Fin r ↪o Fin n) (t : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin r)).filter fun i => (f i).val < t).card

private theorem prefixBase_range {n r : ℕ} (f : Fin r ↪o Fin n) (t : ℕ) :
    prefixBase (range f) t = countBelow f t := by
  classical
  unfold prefixBase countBelow
  conv_rhs => rw [← Finset.card_map f.toEmbedding]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_range, Finset.mem_map]
  constructor
  · rintro ⟨hx, i, hi⟩
    exact ⟨i, hi.symm ▸ hx, hi⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨hi, i, rfl⟩

/-- Comparing all prefix counts inverts the pointwise comparison of the sorted elements. -/
private theorem prefixBase_range_le_iff {n r : ℕ} (f g : Fin r ↪o Fin n) :
    (∀ t ≤ n, prefixBase (range f) t ≤ prefixBase (range g) t) ↔ ∀ i, g i ≤ f i := by
  constructor
  · intro h i
    by_contra! hlt
    let t := (f i).val + 1
    have ht : t ≤ n := (f i).isLt
    have hCount := h t ht
    rw [prefixBase_range, prefixBase_range] at hCount
    have hf : (Finset.Iic i : Finset (Fin r)) ⊆ Finset.univ.filter (fun j => (f j).val < t) := by
      intro j hj
      have hji : j ≤ i := Finset.mem_Iic.mp hj
      have hfji : (f j).val ≤ (f i).val := f.monotone hji
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp [t]; omega⟩
    have hg : (Finset.univ.filter fun j => (g j).val < t) ⊆ Finset.Iio i := by
      intro j hj
      have hgj := (Finset.mem_filter.mp hj).2
      apply Finset.mem_Iio.mpr
      by_contra! hji
      have hgij : (g i).val ≤ (g j).val := g.monotone hji
      change (f i).val < (g i).val at hlt
      dsimp [t] at hgj
      omega
    have hLower := Finset.card_le_card hf
    have hUpper := Finset.card_le_card hg
    rw [Fin.card_Iic] at hLower
    rw [Fin.card_Iio] at hUpper
    unfold countBelow at hCount
    omega
  · intro h t _
    rw [prefixBase_range, prefixBase_range]
    unfold countBelow
    apply Finset.card_le_card
    intro i hi
    have hf := (Finset.mem_filter.mp hi).2
    have hg : (g i).val ≤ (f i).val := h i
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg.trans_lt hf⟩

private theorem prefixNorth_eq_prefixBase {n : ℕ} (p : Path n) (B : Set (Fin n))
    (h : ∀ i, i ∈ B ↔ p i = true) (t : ℕ) : prefixNorth p t = prefixBase B t := by
  classical
  unfold prefixNorth prefixBase
  congr 1
  ext i
  simp [h]

/-- The basis model with each interval row between successive separators. -/
structure IsChainPresentation {n r : ℕ} (M : Matroid (Fin n)) (sep : Fin (r + 1) ↪o Fin n) : Prop where
  first : (sep 0).val = 0
  last : (sep (Fin.last r)).val = n - 1
  bases (B : Set (Fin n)) : M.IsBase B ↔ ∃ b : Fin r ↪ Fin n, range b = B ∧
    ∀ i, sep i.castSucc ≤ b i ∧ b i ≤ sep i.succ

private theorem strictMono_chain_representatives {n r : ℕ} (sep : Fin (r + 1) ↪o Fin n) (b : Fin r ↪ Fin n)
    (hb : ∀ i, sep i.castSucc ≤ b i ∧ b i ≤ sep i.succ) : StrictMono b := by
  intro i j hij
  have hSep : i.succ ≤ j.castSucc := by
    change i.val + 1 ≤ j.val
    exact hij
  have hLe := (hb i).2.trans ((sep.monotone hSep).trans (hb j).1)
  exact lt_of_le_of_ne hLe (fun hEq => hij.ne (b.injective hEq))

/-- The union of the north positions of the two boundaries gives the separator chain. -/
theorem IsRibbonPresentation.exists_chain {n r : ℕ} {M : Matroid (Fin n)} {lower upper : Path n}
    (h : IsRibbonPresentation M r lower upper) :
    ∃ sep : Fin (r + 1) ↪o Fin n, IsChainPresentation M sep := by
  classical
  have hLen := h.length_ge_two
  have hN : 0 < n := by omega
  let first : Fin n := ⟨0, hN⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have hFirstSteps : lower first = false ∧ upper first = true := h.first_steps hN
  have hLastSteps : lower last = true ∧ upper last = false := h.last_steps hN
  let U := (Finset.univ : Finset (Fin n)).filter (fun i => upper i = true)
  let S := insert last U
  have hMemU (i : Fin n) : i ∈ U ↔ upper i = true := by simp [U]
  have hCardU : U.card = r := by
    rw [← h.endpoint_upper, prefixNorth]
    congr 1
    ext i
    simp [U, i.isLt]
  have hLastNot : last ∉ U := by simp [hMemU, hLastSteps.2]
  have hCardS : S.card = r + 1 := by rw [Finset.card_insert_of_notMem hLastNot, hCardU]
  let sep := S.orderEmbOfFin hCardS
  have hSepMem (x : Fin n) : x ∈ range sep ↔ x = last ∨ upper x = true := by
    change x ∈ range (S.orderEmbOfFin hCardS) ↔ _
    rw [Finset.range_orderEmbOfFin]
    simp [S, hMemU]
  have hFirst : sep 0 = first := by
    obtain ⟨j, hj⟩ := (hSepMem first).mpr (Or.inr hFirstSteps.2)
    have hh := sep.monotone (Fin.zero_le j)
    rw [hj] at hh
    apply Fin.ext
    change (sep 0).val ≤ 0 at hh
    change (sep 0).val = 0
    omega
  have hLast : sep (Fin.last r) = last := by
    obtain ⟨j, hj⟩ := (hSepMem last).mpr (Or.inl rfl)
    have hh := sep.monotone (Fin.le_last j)
    rw [hj] at hh
    have hLt := (sep (Fin.last r)).isLt
    apply Fin.ext
    change n - 1 ≤ (sep (Fin.last r)).val at hh
    change (sep (Fin.last r)).val = n - 1
    omega
  let u := (Fin.castSuccOrderEmb (n := r)).trans sep
  let l := (Fin.succOrderEmb r).trans sep
  have hUP (x : Fin n) : x ∈ range u ↔ upper x = true := by
    constructor
    · rintro ⟨j, rfl⟩
      change upper (sep j.castSucc) = true
      rcases (hSepMem (sep j.castSucc)).mp ⟨j.castSucc, rfl⟩ with hEnd | hTop
      · have hj := congrArg Fin.val (sep.injective (hEnd.trans hLast.symm))
        simp at hj
        exact (Nat.ne_of_lt j.isLt hj).elim
      · exact hTop
    · intro hx
      obtain ⟨j, hj⟩ := (hSepMem x).mpr (.inr hx)
      have hj' : j.val ≠ r := by
        intro he
        have hLast' : j = Fin.last r := Fin.ext he
        rw [hLast', hLast] at hj
        rw [← hj, hLastSteps.2] at hx
        contradiction
      have hLess : j.val < r := by have hjLt := j.isLt; omega
      exact ⟨⟨j.val, hLess⟩, hj⟩
  have hLP (x : Fin n) : x ∈ range l ↔ lower x = true := by
    constructor
    · rintro ⟨j, rfl⟩
      change lower (sep j.succ) = true
      by_cases hAtLast : sep j.succ = last
      · rw [hAtLast, hLastSteps.1]
      have hAtFirst : sep j.succ ≠ first := by
        intro he
        have hj := congrArg Fin.val (sep.injective (he.trans hFirst.symm))
        simp at hj
      have ht0 : 0 < (sep j.succ).val := by
        apply Nat.pos_of_ne_zero
        intro he
        exact hAtFirst (Fin.ext he)
      have htLast : (sep j.succ).val + 1 < n := by
        apply lt_of_not_ge
        intro hz
        have he : n = (sep j.succ).val + 1 := le_antisymm hz (sep j.succ).isLt
        exact hAtLast (Fin.ext (by change (sep j.succ).val = n - 1; simp [he]))
      rw [h.inner_step_eq (sep j.succ) ht0 htLast]
      exact ((hSepMem (sep j.succ)).mp ⟨j.succ, rfl⟩).resolve_left hAtLast
    · intro hx
      have hNe : x ≠ first := by
        intro he
        rw [he, hFirstSteps.1] at hx
        contradiction
      have hS : x ∈ range sep := by
        apply (hSepMem x).mpr
        by_cases hAtLast : x = last
        · exact Or.inl hAtLast
        have ht0 : 0 < x.val := by
          apply Nat.pos_of_ne_zero
          intro he
          exact hNe (Fin.ext he)
        have htLast : x.val + 1 < n := by
          apply lt_of_not_ge
          intro hz
          have he : n = x.val + 1 := le_antisymm hz x.isLt
          exact hAtLast (Fin.ext (by change x.val = n - 1; simp [he]))
        exact Or.inr ((h.inner_step_eq x ht0 htLast).symm ▸ hx)
      obtain ⟨j, hj⟩ := hS
      have hPos : 0 < j.val := by
        apply Nat.pos_of_ne_zero
        intro hj0
        have hj' : j = 0 := Fin.ext hj0
        rw [hj', hFirst] at hj
        exact hNe hj.symm
      have hjLt := j.isLt
      let i : Fin r := ⟨j.val - 1, by omega⟩
      have hi : i.succ = j := Fin.ext (by change j.val - 1 + 1 = j.val; omega)
      refine ⟨i, ?_⟩
      change sep i.succ = x
      rwa [hi]
  have hUp (t : ℕ) := prefixNorth_eq_prefixBase upper (range u) hUP t
  have hLo (t : ℕ) := prefixNorth_eq_prefixBase lower (range l) hLP t
  refine ⟨sep, ⟨congrArg Fin.val hFirst, congrArg Fin.val hLast, ?_⟩⟩
  intro B
  constructor
  · intro hB
    letI : Fintype B := Fintype.ofFinite _
    have hEnd := (h.bases B).mp hB n le_rfl
    rw [h.endpoint_lower, h.endpoint_upper, prefixBase_length] at hEnd
    have hBC : B.toFinset.card = r := by
      rw [← Set.ncard_eq_toFinset_card']
      exact le_antisymm hEnd.2 hEnd.1
    let b := B.toFinset.orderEmbOfFin hBC
    have hb : range b = B := by
      change range (B.toFinset.orderEmbOfFin hBC) = B
      simp [Finset.range_orderEmbOfFin]
    have hBelow : ∀ t ≤ n, prefixBase (range l) t ≤ prefixBase (range b) t := by
      intro t ht
      rw [← hLo, hb]
      exact ((h.bases B).mp hB t ht).1
    have hAbove : ∀ t ≤ n, prefixBase (range b) t ≤ prefixBase (range u) t := by
      intro t ht
      rw [← hUp, hb]
      exact ((h.bases B).mp hB t ht).2
    exact ⟨b.toEmbedding, hb, fun i =>
      ⟨(prefixBase_range_le_iff b u).mp hAbove i, (prefixBase_range_le_iff l b).mp hBelow i⟩⟩
  · rintro ⟨b, hb, hBounds⟩
    let b' : Fin r ↪o Fin n := OrderEmbedding.ofStrictMono b (strictMono_chain_representatives sep b hBounds)
    have hb' : range b' = B := hb
    apply (h.bases B).mpr
    intro t ht
    rw [hLo, hUp, ← hb']
    exact ⟨(prefixBase_range_le_iff l b').mpr (fun i => (hBounds i).2) t ht,
      (prefixBase_range_le_iff b' u).mpr (fun i => (hBounds i).1) t ht⟩

#print axioms IsRibbonPresentation.exists_chain

end Ribbon.Source
