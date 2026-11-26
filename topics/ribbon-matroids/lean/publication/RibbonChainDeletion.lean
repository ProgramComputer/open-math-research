import Mathlib.Order.Interval.Finset.Fin
import RibbonChainPresentation
import OpenMathResearch.MatroidKLSplitDeletion

/-!
# Deleting labels between the separators

Contracting an intervening label fixes its row in the basis representatives. Splice the choices on either side of that row. The two boundary chains certify the closure witnesses by counting representatives.
-/

open Set Matroid

namespace Ribbon.Source

/-- The chain retains all separators, and its choices use only labels still in the ground set. -/
structure IsRestrictedChain {n r : ℕ} (M : Matroid (Fin n)) (sep : Fin (r + 1) ↪o Fin n) : Prop where
  sep_ground (i : Fin (r + 1)) : sep i ∈ M.E
  bases (B : Set (Fin n)) : M.IsBase B ↔ B ⊆ M.E ∧ ∃ b : Fin r ↪ Fin n, range b = B ∧
    ∀ i, sep i.castSucc ≤ b i ∧ b i ≤ sep i.succ

theorem IsChainPresentation.restricted {n r : ℕ} {M : Matroid (Fin n)} {sep : Fin (r + 1) ↪o Fin n}
    (h : IsChainPresentation M sep) (hg : M.E = Set.univ) : IsRestrictedChain M sep := by
  constructor
  · intro i
    simp [hg]
  · intro B
    simpa [hg] using h.bases B

variable {n r : ℕ} {M : Matroid (Fin n)} {sep : Fin (r + 1) ↪o Fin n}

private def lowerRepresentatives (sep : Fin (r + 1) ↪o Fin n) : Fin r ↪ Fin n :=
  ((Fin.castSuccOrderEmb (n := r)).trans sep).toEmbedding

private def upperRepresentatives (sep : Fin (r + 1) ↪o Fin n) : Fin r ↪ Fin n :=
  ((Fin.succOrderEmb r).trans sep).toEmbedding

private theorem sep_le_join (g : Fin (r + 1) ↪o Fin n) (i : Fin r) : g i.castSucc ≤ g i.succ :=
  g.monotone (by change i.val ≤ i.val + 1; omega)

theorem IsRestrictedChain.lower_base (h : IsRestrictedChain M sep) :
    M.IsBase (range (lowerRepresentatives sep)) := by
  apply (h.bases _).mpr
  refine ⟨?_, ⟨lowerRepresentatives sep, rfl, fun i => ⟨le_rfl, sep_le_join sep i⟩⟩⟩
  rintro _ ⟨i, rfl⟩
  exact h.sep_ground i.castSucc

theorem IsRestrictedChain.upper_base (h : IsRestrictedChain M sep) :
    M.IsBase (range (upperRepresentatives sep)) := by
  apply (h.bases _).mpr
  refine ⟨?_, ⟨upperRepresentatives sep, rfl, fun i => ⟨sep_le_join sep i, le_rfl⟩⟩⟩
  rintro _ ⟨i, rfl⟩
  exact h.sep_ground i.succ

theorem IsRestrictedChain.spans_without_nonseparator (h : IsRestrictedChain M sep) {e : Fin n}
    (he : e ∉ range sep) : M.Spanning (M.E \ {e}) := by
  apply (Matroid.spanning_iff_exists_isBase_subset Set.sdiff_subset).mpr
  refine ⟨_, h.lower_base, ?_⟩
  rintro x ⟨i, rfl⟩
  refine ⟨h.sep_ground i.castSucc, ?_⟩
  intro hf
  exact he ⟨i.castSucc, Set.mem_singleton_iff.mp hf⟩

theorem IsRestrictedChain.delete_nonseparator (h : IsRestrictedChain M sep) {e : Fin n}
    (he : e ∉ range sep) : IsRestrictedChain (M ＼ {e}) sep := by
  have hSpan := h.spans_without_nonseparator he
  constructor
  · intro i
    rw [Matroid.delete_ground]
    exact ⟨h.sep_ground i, fun hn => he ⟨i, Set.mem_singleton_iff.mp hn⟩⟩
  · intro B
    rw [Matroid.delete_isBase_iff, Matroid.delete_ground]
    constructor
    · intro hB
      have hBase := hB.isBasis_closure_right
      rw [hSpan.closure_eq_of_superset Set.Subset.rfl, Matroid.isBasis_ground_iff] at hBase
      exact ⟨hB.subset, ((h.bases B).mp hBase).2⟩
    · rintro ⟨hBG, hb⟩
      have hB : M.IsBase B := (h.bases B).mpr ⟨hBG.trans Set.sdiff_subset, hb⟩
      exact hB.isBasis_ground.isBasis_subset hBG Set.sdiff_subset

private theorem sep_ne_of_inside {k : Fin r} {e : Fin n} (hLo : sep k.castSucc < e) (hHi : e < sep k.succ) :
    e ∉ range sep := by
  rintro ⟨i, rfl⟩
  by_cases hi : i ≤ k.castSucc
  · exact not_le_of_gt hLo (sep.monotone hi)
  · have hi' : k.succ ≤ i := by
      change ¬ i.val ≤ k.val at hi
      change k.val + 1 ≤ i.val
      omega
    exact not_le_of_gt hHi (sep.monotone hi')

private theorem indep_singleton_of_inside (h : IsRestrictedChain M sep) {k : Fin r} {e : Fin n}
    (he : e ∈ M.E) (hLo : sep k.castSucc < e) (hHi : e < sep k.succ) : M.Indep {e} := by
  classical
  let rep : Fin r → Fin n := fun i => if i = k then e else sep i.castSucc
  have hNot := sep_ne_of_inside hLo hHi
  let b : Fin r ↪ Fin n := ⟨rep, by
    intro i j hEq
    change rep i = rep j at hEq
    by_cases hi : i = k <;> by_cases hj : j = k
    · exact hi.trans hj.symm
    · simp [rep, hi, hj] at hEq
      exact (hNot ⟨j.castSucc, hEq.symm⟩).elim
    · simp [rep, hi, hj] at hEq
      exact (hNot ⟨i.castSucc, hEq⟩).elim
    · simp [rep, hi, hj] at hEq
      exact hEq⟩
  have hB : M.IsBase (range b) := by
    apply (h.bases _).mpr
    refine ⟨?_, ⟨b, rfl, ?_⟩⟩
    · rintro x ⟨i, rfl⟩
      change rep i ∈ M.E
      by_cases hi : i = k <;> simp [rep, hi, he, h.sep_ground]
    · intro i
      change sep i.castSucc ≤ rep i ∧ rep i ≤ sep i.succ
      by_cases hi : i = k
      · subst i
        simpa [rep] using And.intro hLo.le hHi.le
      · simp only [rep, if_neg hi, le_refl, true_and]
        exact sep_le_join sep i
  apply hB.indep.subset
  apply Set.singleton_subset_iff.mpr
  exact ⟨k, by change rep k = e; simp [rep]⟩

private theorem rep_below_cut {b : Fin r ↪ Fin n} {k i : Fin r} {e : Fin n}
    (hb : ∀ j, sep j.castSucc ≤ b j ∧ b j ≤ sep j.succ) (hLo : sep k.castSucc < e)
    (hi : i < k) : b i < e := by
  have hle : i.succ ≤ k.castSucc := by change i.val + 1 ≤ k.val; exact hi
  exact ((hb i).2.trans (sep.monotone hle)).trans_lt hLo

private theorem rep_above_cut {b : Fin r ↪ Fin n} {k i : Fin r} {e : Fin n}
    (hb : ∀ j, sep j.castSucc ≤ b j ∧ b j ≤ sep j.succ) (hHi : e < sep k.succ)
    (hi : k < i) : e < b i := by
  have hle : k.succ ≤ i.castSucc := by change k.val + 1 ≤ i.val; exact hi
  exact (hHi.trans_le (sep.monotone hle)).trans_le (hb i).1

/-- Contracting a label strictly between separators splits independence across that label. -/
theorem IsRestrictedChain.contract_splitsAt (h : IsRestrictedChain M sep) {k : Fin r} {e : Fin n}
    (he : e ∈ M.E) (hLo : sep k.castSucc < e) (hHi : e < sep k.succ) :
    OpenMathResearch.MatroidKL.SplitsAt (M ／ ({e} : Set (Fin n))) {x | x < e} := by
  apply OpenMathResearch.MatroidKL.splitsAt_of_baseSplice
  intro B C hB hC
  have hI := indep_singleton_of_inside h he hLo hHi
  obtain ⟨hBaseB, hDisjB⟩ := hI.contract_isBase_iff.mp hB
  obtain ⟨hBaseC, hDisjC⟩ := hI.contract_isBase_iff.mp hC
  obtain ⟨_, b, hb, hBoundsB⟩ := (h.bases _).mp hBaseB
  obtain ⟨_, c, hc, hBoundsC⟩ := (h.bases _).mp hBaseC
  have center (a : Fin r ↪ Fin n) (ha : e ∈ range a)
      (hBounds : ∀ j, sep j.castSucc ≤ a j ∧ a j ≤ sep j.succ) : a k = e := by
    obtain ⟨j, hj⟩ := ha
    rcases lt_trichotomy j k with hlt | rfl | hgt
    · exact (ne_of_lt (rep_below_cut hBounds hLo hlt) hj).elim
    · exact hj
    · exact (ne_of_gt (rep_above_cut hBounds hHi hgt) hj).elim
  have hbMid := center b (by rw [hb]; exact Or.inr (Set.mem_singleton e)) hBoundsB
  have hcMid := center c (by rw [hc]; exact Or.inr (Set.mem_singleton e)) hBoundsC
  have hbCut (i : Fin r) : b i < e ↔ i < k := by
    constructor
    · intro hi
      by_contra! hki
      rcases lt_or_eq_of_le hki with hk | rfl
      · exact (rep_above_cut hBoundsB hHi hk).not_le hi.le
      · exact hi.ne hbMid
    · exact rep_below_cut hBoundsB hLo
  have hcCut (i : Fin r) : c i < e ↔ i < k := by
    constructor
    · intro hi
      by_contra! hki
      rcases lt_or_eq_of_le hki with hk | rfl
      · exact (rep_above_cut hBoundsC hHi hk).not_le hi.le
      · exact hi.ne hcMid
    · exact rep_below_cut hBoundsC hLo
  let splice : Fin r → Fin n := fun i => if i < k then b i else c i
  let d : Fin r ↪ Fin n := ⟨splice, by
    intro i j hh
    change splice i = splice j at hh
    by_cases hi : i < k <;> by_cases hj : j < k
    · exact b.injective (by simpa [splice, hi, hj] using hh)
    · have heq : b i = c j := by simpa [splice, hi, hj] using hh
      have hlt : c j < e := heq ▸ (hbCut i).mpr hi
      exact (hj ((hcCut j).mp hlt)).elim
    · have heq : c i = b j := by simpa [splice, hi, hj] using hh
      have hlt : c i < e := heq.symm ▸ (hbCut j).mpr hj
      exact (hi ((hcCut i).mp hlt)).elim
    · exact c.injective (by simpa [splice, hi, hj] using hh)⟩
  let D := (B ∩ {x | x < e}) ∪ (C \ {x | x < e})
  have hRange : range d = D ∪ {e} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      change splice i ∈ D ∪ {e}
      by_cases hi : i < k
      · rw [show splice i = b i from if_pos hi]
        have hlt : b i < e := (hbCut i).mpr hi
        have hmem : b i ∈ B ∪ {e} := hb ▸ (Set.mem_range_self i : b i ∈ range b)
        exact Or.inl (Or.inl ⟨hmem.resolve_right (by simpa using hlt.ne), hlt⟩)
      · rw [show splice i = c i from if_neg hi]
        have hmem : c i ∈ C ∪ {e} := hc ▸ (Set.mem_range_self i : c i ∈ range c)
        exact hmem.imp_left (fun hC' => Or.inr ⟨hC', fun hc' => hi ((hcCut i).mp hc')⟩)
    · intro hx
      rcases hx with hx | hx
      · rcases hx with hxB | hxC
        · have hmem : x ∈ range b := hb.symm ▸ (Or.inl hxB.1 : x ∈ B ∪ {e})
          obtain ⟨i, hi⟩ := hmem
          have hlt : i < k := (hbCut i).mp (hi.symm ▸ hxB.2)
          exact ⟨i, by change splice i = x; simp [splice, hlt, hi]⟩
        · have hmem : x ∈ range c := hc.symm ▸ (Or.inl hxC.1 : x ∈ C ∪ {e})
          obtain ⟨i, hi⟩ := hmem
          have hnl : ¬i < k := fun hk => hxC.2 (hi ▸ (hcCut i).mpr hk)
          exact ⟨i, by change splice i = x; simp [splice, hnl, hi]⟩
      · have hxE : x = e := Set.mem_singleton_iff.mp hx
        subst x
        exact ⟨k, by change splice k = e; simp [splice, hcMid]⟩
  apply hI.contract_isBase_iff.mpr
  refine ⟨(h.bases _).mpr ⟨?_, ⟨d, hRange, ?_⟩⟩, ?_⟩
  · apply Set.union_subset
    · exact Set.union_subset (Set.inter_subset_left.trans (Set.subset_union_left.trans hBaseB.subset_ground))
        (Set.sdiff_subset.trans (Set.subset_union_left.trans hBaseC.subset_ground))
    · exact Set.singleton_subset_iff.mpr he
  · intro i
    change sep i.castSucc ≤ splice i ∧ splice i ≤ sep i.succ
    by_cases hi : i < k <;> simp [splice, hi, hBoundsB, hBoundsC]
  · exact (hDisjB.mono_left Set.inter_subset_left).union_left (hDisjC.mono_left Set.sdiff_subset)

private theorem card_indep_below {e : Fin n} {k : Fin r} (h : IsRestrictedChain M sep)
    (hHi : e < sep k.succ) (S : Finset (Fin n)) (hS : M.Indep (S : Set (Fin n)))
    (hBelow : ∀ x ∈ S, x ≤ e) : S.card ≤ k.val + 1 := by
  obtain ⟨B, hB, hSB⟩ := hS.exists_isBase_superset
  obtain ⟨_, b, hb, hBounds⟩ := (h.bases _).mp hB
  have hSub : S ⊆ (Finset.Iic k).map b := by
    intro x hx
    have hRange : x ∈ range b := hb.symm ▸ hSB hx
    obtain ⟨i, hi⟩ := hRange
    have hki : i ≤ k := by
      by_contra! hWrong
      have hGt := rep_above_cut hBounds hHi hWrong
      rw [hi] at hGt
      exact (not_le_of_gt hGt) (hBelow x hx)
    exact Finset.mem_map.mpr ⟨i, Finset.mem_Iic.mpr hki, hi⟩
  have hCard := Finset.card_le_card hSub
  rwa [Finset.card_map, Fin.card_Iic] at hCard

private theorem card_indep_above {e : Fin n} {k : Fin r} (h : IsRestrictedChain M sep)
    (hLo : sep k.castSucc < e) (S : Finset (Fin n)) (hS : M.Indep (S : Set (Fin n)))
    (hAbove : ∀ x ∈ S, e ≤ x) : S.card ≤ r - k.val := by
  obtain ⟨B, hB, hSB⟩ := hS.exists_isBase_superset
  obtain ⟨_, b, hb, hBounds⟩ := (h.bases _).mp hB
  have hSub : S ⊆ (Finset.Ici k).map b := by
    intro x hx
    have hRange : x ∈ range b := hb.symm ▸ hSB hx
    obtain ⟨i, hi⟩ := hRange
    have hki : k ≤ i := by
      by_contra! hWrong
      have hLt := rep_below_cut hBounds hLo hWrong
      rw [hi] at hLt
      exact (not_le_of_gt hLt) (hAbove x hx)
    exact Finset.mem_map.mpr ⟨i, Finset.mem_Ici.mpr hki, hi⟩
  have hCard := Finset.card_le_card hSub
  rwa [Finset.card_map, Fin.card_Ici] at hCard

private theorem IsRestrictedChain.left_closure_witness (h : IsRestrictedChain M sep) {k : Fin r} {e : Fin n}
    (he : e ∈ M.E) (hLo : sep k.castSucc < e) (hHi : e < sep k.succ) :
    ∃ A : Set (Fin n), A ⊆ M.E \ {e} ∧ A ⊆ {x | x < e} ∧ e ∈ M.closure A := by
  classical
  let A := (Finset.Iic k.castSucc).map sep.toEmbedding
  have hA_lt {x} (hx : x ∈ A) : x < e := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    exact (sep.monotone (Finset.mem_Iic.mp hi)).trans_lt hLo
  have hAF : (A : Set (Fin n)) ⊆ M.E \ {e} := by
    intro x hx
    refine ⟨?_, by simpa using (hA_lt hx).ne⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    exact h.sep_ground i
  refine ⟨A, hAF, fun _ hx => hA_lt hx, ?_⟩
  have hI : M.Indep (A : Set (Fin n)) := by
    apply h.lower_base.indep.subset
    intro x hx
    obtain ⟨i, hi, hEq⟩ := Finset.mem_map.mp hx
    have hLeFin : i ≤ k.castSucc := Finset.mem_Iic.mp hi
    have hLe : i.val ≤ k.val := hLeFin
    let j : Fin r := ⟨i.val, hLe.trans_lt k.isLt⟩
    exact ⟨j, by change sep j.castSucc = x; rw [show j.castSucc = i from Fin.ext rfl]; exact hEq⟩
  apply hI.mem_closure_iff'.mpr
  refine ⟨he, ?_⟩
  intro hInsert
  exfalso
  have hE : e ∉ A := fun hx => (hA_lt hx).false
  have hIndep : M.Indep ((insert e A : Finset (Fin n)) : Set (Fin n)) := by simpa using hInsert
  have hSize := card_indep_below h hHi (insert e A) hIndep (by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxA
    · exact le_rfl
    · exact (hA_lt hxA).le)
  rw [Finset.card_insert_of_notMem hE, Finset.card_map, Fin.card_Iic] at hSize
  change k.val + 1 + 1 ≤ k.val + 1 at hSize
  omega

private theorem IsRestrictedChain.right_closure_witness (h : IsRestrictedChain M sep) {k : Fin r} {e : Fin n}
    (he : e ∈ M.E) (hLo : sep k.castSucc < e) (hHi : e < sep k.succ) :
    ∃ A : Set (Fin n), A ⊆ M.E \ {e} ∧ Disjoint A {x | x < e} ∧ e ∈ M.closure A := by
  classical
  let A := (Finset.Ici k.succ).map sep.toEmbedding
  have hA_gt {x} (hx : x ∈ A) : e < x := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    exact hHi.trans_le (sep.monotone (Finset.mem_Ici.mp hi))
  have hAF : (A : Set (Fin n)) ⊆ M.E \ {e} := by
    intro x hx
    refine ⟨?_, by simpa using (hA_gt hx).ne.symm⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    exact h.sep_ground i
  refine ⟨A, hAF, Set.disjoint_left.mpr (fun _ hx hlt => (not_le_of_gt (hA_gt hx)) hlt.le), ?_⟩
  have hI : M.Indep (A : Set (Fin n)) := by
    apply h.upper_base.indep.subset
    intro x hx
    obtain ⟨i, hi, hEq⟩ := Finset.mem_map.mp hx
    have hLoFin : k.succ ≤ i := Finset.mem_Ici.mp hi
    have hLo' : k.val + 1 ≤ i.val := hLoFin
    have hiLt := i.isLt
    let j : Fin r := ⟨i.val - 1, by omega⟩
    have hJ : j.succ = i := Fin.ext (by change i.val - 1 + 1 = i.val; omega)
    exact ⟨j, by change sep j.succ = x; rwa [hJ]⟩
  apply hI.mem_closure_iff'.mpr
  refine ⟨he, ?_⟩
  intro hInsert
  exfalso
  have hE : e ∉ A := fun hx => (hA_gt hx).false
  have hIndep : M.Indep ((insert e A : Finset (Fin n)) : Set (Fin n)) := by simpa using hInsert
  have hSize := card_indep_above h hLo (insert e A) hIndep (by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxA
    · exact le_rfl
    · exact (hA_gt hxA).le)
  rw [Finset.card_insert_of_notMem hE, Finset.card_map, Fin.card_Ici] at hSize
  change r + 1 - (k.val + 1) + 1 ≤ r - k.val at hSize
  omega

/-- The Z-polynomial survives deleting any label strictly between two consecutive separators. -/
theorem IsRestrictedChain.matroidZ_delete_of_inside (h : IsRestrictedChain M sep) {k : Fin r} {e : Fin n}
    (he : e ∈ M.E) (hLo : sep k.castSucc < e) (hHi : e < sep k.succ) :
    OpenMathResearch.MatroidKL.matroidZ M = OpenMathResearch.MatroidKL.matroidZ (M ＼ {e}) := by
  obtain ⟨A, hAE, hAS, hAc⟩ := h.left_closure_witness he hLo hHi
  obtain ⟨B, hBE, hBS, hBc⟩ := h.right_closure_witness he hLo hHi
  exact OpenMathResearch.MatroidKL.matroidZ_delete_of_split M e {x | x < e} A B
    (h.spans_without_nonseparator (sep_ne_of_inside hLo hHi)) (h.contract_splitsAt he hLo hHi)
    hAE hAS hAc hBE hBS hBc

#print axioms IsRestrictedChain.delete_nonseparator
#print axioms IsRestrictedChain.contract_splitsAt
#print axioms IsRestrictedChain.matroidZ_delete_of_inside

end Ribbon.Source
