import Mathlib.Data.Finset.Max
import RibbonChainDeletion

/-!
# Reduction to the separator circuit

Delete the intervening labels one at a time. When only separators remain, every basis omits one separator, and every such set is represented by the order embedding that skips that position.
-/

open Set Matroid

namespace Ribbon.Source

private theorem lies_between_separators {n r : ℕ} (sep : Fin (r + 1) ↪o Fin n)
    (hFirst : (sep 0).val = 0) (hLast : (sep (Fin.last r)).val = n - 1) {e : Fin n}
    (he : e ∉ range sep) : ∃ k : Fin r, sep k.castSucc < e ∧ e < sep k.succ := by
  let S := (Finset.univ : Finset (Fin (r + 1))).filter fun i => e < sep i
  have hEnd : e < sep (Fin.last r) := by
    apply lt_of_le_of_ne
    · change e.val ≤ (sep (Fin.last r)).val
      rw [hLast]
      have heLt := e.isLt
      omega
    · exact fun hEq => he ⟨Fin.last r, hEq.symm⟩
  have hS : S.Nonempty := ⟨Fin.last r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hEnd⟩⟩
  let i := S.min' hS
  have hi := (Finset.mem_filter.mp (S.min'_mem hS)).2
  have hPos : 0 < i.val := by
    apply Nat.pos_of_ne_zero
    intro hZero
    have hii : i = 0 := Fin.ext hZero
    change e < sep i at hi
    rw [hii] at hi
    change e.val < (sep 0).val at hi
    omega
  have hiLt := i.isLt
  let k : Fin r := ⟨i.val - 1, by omega⟩
  have hKi : k.succ = i := Fin.ext (by change i.val - 1 + 1 = i.val; omega)
  refine ⟨k, ?_, by simpa only [hKi] using hi⟩
  by_contra! hWrong
  have heL : e < sep k.castSucc := lt_of_le_of_ne hWrong fun hEq => he ⟨k.castSucc, hEq.symm⟩
  have hL : k.castSucc ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, heL⟩
  have hLeast : i ≤ k.castSucc := Finset.min'_le _ _ hL
  rw [← hKi] at hLeast
  change k.val + 1 ≤ k.val at hLeast
  omega

/-- Delete every label lying between separators without changing the Z-polynomial. -/
theorem IsRestrictedChain.reduce_to_separators {n r : ℕ} {M : Matroid (Fin n)}
    {sep : Fin (r + 1) ↪o Fin n} (h : IsRestrictedChain M sep)
    (hFirst : (sep 0).val = 0) (hLast : (sep (Fin.last r)).val = n - 1) :
    ∃ N : Matroid (Fin n), N.E = range sep ∧ IsRestrictedChain N sep ∧
      OpenMathResearch.MatroidKL.matroidZ M = OpenMathResearch.MatroidKL.matroidZ N := by
  classical
  suffices hm : ∀ d (P : Matroid (Fin n)), (P.E \ range sep).ncard = d → IsRestrictedChain P sep →
      ∃ N : Matroid (Fin n), N.E = range sep ∧ IsRestrictedChain N sep ∧
        OpenMathResearch.MatroidKL.matroidZ P = OpenMathResearch.MatroidKL.matroidZ N by
    exact hm _ M rfl h
  intro d
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    intro P hd hP
    by_cases hGround : P.E ⊆ range sep
    · refine ⟨P, Set.Subset.antisymm hGround ?_, hP, rfl⟩
      rintro _ ⟨i, rfl⟩
      exact hP.sep_ground i
    obtain ⟨e, heE, he⟩ := Set.not_subset.mp hGround
    obtain ⟨k, hLo, hHi⟩ := lies_between_separators sep hFirst hLast he
    let Q := P ＼ ({e} : Set (Fin n))
    have hLess : (Q.E \ range sep).ncard < d := by
      rw [← hd, show Q.E = P.E \ {e} from P.delete_ground {e}]
      apply Set.ncard_lt_ncard (ht := Set.toFinite _)
      refine lt_of_le_of_ne (fun _ hx => ⟨hx.1.1, hx.2⟩) ?_
      intro hEq
      have heQ : e ∈ (P.E \ {e}) \ range sep := hEq.symm ▸ (show e ∈ P.E \ range sep from ⟨heE, he⟩)
      exact heQ.1.2 (Set.mem_singleton e)
    obtain ⟨N, hN, hChain, hZ⟩ := ih _ hLess Q rfl (hP.delete_nonseparator he)
    exact ⟨N, hN, hChain, (hP.matroidZ_delete_of_inside heE hLo hHi).trans hZ⟩

private theorem ncard_range_finEmb {s n : ℕ} (f : Fin s ↪ Fin n) : (Set.range f).ncard = s := by
  rw [← Set.image_univ, Set.ncard_image_of_injective _ f.injective, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-- A chain with only separator labels has the rank-r circuit basis rule. -/
theorem IsRestrictedChain.isBase_iff_of_ground_sep {n r : ℕ} {M : Matroid (Fin n)}
    {sep : Fin (r + 1) ↪o Fin n} (h : IsRestrictedChain M sep) (hg : M.E = range sep) (B : Set (Fin n)) :
    M.IsBase B ↔ B ⊆ M.E ∧ B.ncard = r := by
  classical
  constructor
  · intro hB
    obtain ⟨hBG, b, hRange, _⟩ := (h.bases B).mp hB
    exact ⟨hBG, hRange ▸ ncard_range_finEmb b⟩
  · rintro ⟨hBG, hCard⟩
    have hGE : M.E.ncard = r + 1 := by rw [hg]; exact ncard_range_finEmb sep.toEmbedding
    have hNot : ¬ M.E ⊆ B := by
      intro hGB
      have hEq := Set.Subset.antisymm hBG hGB
      rw [hEq, hGE] at hCard
      omega
    obtain ⟨e, heG, heB⟩ := Set.not_subset.mp hNot
    obtain ⟨j, hj⟩ := (hg ▸ heG : e ∈ range sep)
    have hCard' : (M.E \ {e}).ncard = r := by
      have hh := Set.ncard_sdiff_singleton_add_one heG
      omega
    have hB : B = M.E \ {e} := by
      apply Set.eq_of_subset_of_ncard_le (ht := Set.toFinite _)
      · intro x hx
        exact ⟨hBG hx, fun heq => heB ((Set.mem_singleton_iff.mp heq) ▸ hx)⟩
      · omega
    let b : Fin r ↪ Fin n := ((Fin.succAboveOrderEmb j).trans sep).toEmbedding
    have hb : range b = B := by
      rw [hB, hg]
      change range (sep ∘ j.succAbove) = range sep \ {e}
      rw [Set.range_comp, Fin.range_succAbove]
      ext x
      constructor
      · rintro ⟨i, hi, rfl⟩
        refine ⟨⟨i, rfl⟩, ?_⟩
        intro hx
        have heq : sep i = e := Set.mem_singleton_iff.mp hx
        exact hi (Set.mem_singleton_iff.mpr (sep.injective (heq.trans hj.symm)))
      · rintro ⟨⟨i, rfl⟩, hx⟩
        refine ⟨i, ?_, rfl⟩
        intro hi
        have hi' : i = j := Set.mem_singleton_iff.mp hi
        exact hx (Set.mem_singleton_iff.mpr (hi' ▸ hj))
    apply (h.bases B).mpr
    refine ⟨hBG, ⟨b, hb, ?_⟩⟩
    intro i
    change sep i.castSucc ≤ sep (j.succAbove i) ∧ sep (j.succAbove i) ≤ sep i.succ
    have hh : sep i.castSucc ≤ sep i.succ := sep.monotone (by change i.val ≤ i.val + 1; omega)
    by_cases hi : i.castSucc < j
    · rw [Fin.succAbove_of_castSucc_lt j i hi]
      exact ⟨le_rfl, hh⟩
    · rw [Fin.succAbove_of_le_castSucc j i (not_lt.mp hi)]
      exact ⟨hh, le_rfl⟩

/-- Every nonempty connected ribbon has the Z-polynomial of a rank-r circuit matroid. -/
theorem IsRibbonPresentation.exists_circuitBoundary {n r : ℕ} {M : Matroid (Fin n)} {lower upper : Path n}
    (h : IsRibbonPresentation M r lower upper) :
    ∃ N : Matroid (Fin n), N.E.ncard = r + 1 ∧
      (∀ B : Set (Fin n), N.IsBase B ↔ B ⊆ N.E ∧ B.ncard = r) ∧
      OpenMathResearch.MatroidKL.matroidZ M = OpenMathResearch.MatroidKL.matroidZ N := by
  obtain ⟨sep, hSep⟩ := h.exists_chain
  obtain ⟨N, hg, hChain, hZ⟩ := (hSep.restricted h.ground_eq).reduce_to_separators hSep.first hSep.last
  refine ⟨N, ?_, hChain.isBase_iff_of_ground_sep hg, hZ⟩
  rw [hg]
  exact ncard_range_finEmb sep.toEmbedding

#print axioms IsRestrictedChain.reduce_to_separators
#print axioms IsRestrictedChain.isBase_iff_of_ground_sep
#print axioms IsRibbonPresentation.exists_circuitBoundary

end Ribbon.Source
