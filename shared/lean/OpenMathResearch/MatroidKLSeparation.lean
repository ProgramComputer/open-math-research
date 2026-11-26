import OpenMathResearch.MatroidKLMap

/-!
# Direct sums from a splicing rule

Splicing bases across a cut splits independence. That condition survives contraction and realizes the matroid as a relabeled direct sum of its two restrictions.
-/

open Set Matroid

noncomputable section

namespace OpenMathResearch.MatroidKL

variable {α : Type*}

/-- Independence splits along a set when the two portions combine to an independent set. -/
def SplitsAt (M : Matroid α) (L : Set α) : Prop :=
  ∀ ⦃I : Set α⦄, I ⊆ M.E → M.Indep (I ∩ L) → M.Indep (I \ L) → M.Indep I

/-- A base-splicing property implies that independence splits along the cut. -/
theorem splitsAt_of_baseSplice (M : Matroid α) (L : Set α)
    (hSplice : ∀ ⦃B C : Set α⦄, M.IsBase B → M.IsBase C → M.IsBase ((B ∩ L) ∪ (C \ L))) :
    SplitsAt M L := by
  intro I _ h₁ h₂
  obtain ⟨B, hB, hIB⟩ := h₁.exists_isBase_superset
  obtain ⟨C, hC, hIC⟩ := h₂.exists_isBase_superset
  apply (hSplice hB hC).indep.subset
  intro e he
  by_cases heL : e ∈ L
  · exact Or.inl ⟨hIB ⟨he, heL⟩, heL⟩
  · exact Or.inr ⟨hIC ⟨he, heL⟩, heL⟩

/-- The same cut splits independence after a contraction. -/
theorem SplitsAt.contract {M : Matroid α} {L : Set α} (h : SplitsAt M L) (C : Set α) :
    SplitsAt (M ／ C) L := by
  intro I hI hLeft hRight
  obtain ⟨J, hJ⟩ := M.exists_isBasis' C
  rw [hJ.contract_indep_iff]
  have hDisj : Disjoint C I := by
    rw [Set.disjoint_left]
    exact fun _ hxC hxI => (hI hxI).2 hxC
  refine ⟨?_, hDisj⟩
  apply h (Set.union_subset (hI.trans Set.sdiff_subset) hJ.indep.subset_ground)
  · apply (hJ.contract_indep_iff.mp hLeft).1.subset
    intro x hX
    exact hX.1.imp (fun hI' => (show x ∈ I ∩ L from ⟨hI', hX.2⟩)) id
  · apply (hJ.contract_indep_iff.mp hRight).1.subset
    intro x hX
    exact hX.1.imp (fun hI' => (show x ∈ I \ L from ⟨hI', hX.2⟩)) id

private def joinSides (a : α ⊕ α) : α := a.elim id id

private theorem joinSides_injOn (M : Matroid α) (L : Set α) :
    Set.InjOn joinSides ((M ↾ (M.E ∩ L)).sum (M ↾ (M.E \ L))).E := by
  classical
  let cut : α → α ⊕ α := fun a => if a ∈ L then Sum.inl a else Sum.inr a
  have hc (a : α ⊕ α) (ha : a ∈ ((M ↾ (M.E ∩ L)).sum (M ↾ (M.E \ L))).E) :
      cut (joinSides a) = a := by
    rw [Matroid.sum_ground, Matroid.restrict_ground_eq, Matroid.restrict_ground_eq] at ha
    cases a with
    | inl e =>
      have he : e ∈ M.E ∩ L := by simpa using ha
      simp [cut, joinSides, he.2]
    | inr e =>
      have he : e ∈ M.E \ L := by simpa using ha
      simp [cut, joinSides, he.2]
  intro a ha b hb hab
  rw [← hc a ha, ← hc b hb, hab]

private theorem joinSides_image (L R : Set α) :
    joinSides '' ((Sum.inl '' L) ∪ (Sum.inr '' R)) = L ∪ R := by
  simp [Set.image_union, Set.image_image, Function.comp_def, joinSides]

/-- A matroid whose independence splits is the relabeling of the direct sum of its restrictions. -/
theorem eq_map_sum_of_splitsAt (M : Matroid α) (L : Set α) (h : SplitsAt M L) :
    M = (((M ↾ (M.E ∩ L)).sum (M ↾ (M.E \ L))).map joinSides (joinSides_injOn M L)) := by
  refine Matroid.ext_indep ?_ ?_
  · rw [Matroid.map_ground, Matroid.sum_ground, Matroid.restrict_ground_eq, Matroid.restrict_ground_eq,
      joinSides_image]
    tauto_set
  · intro I hI
    rw [Matroid.map_indep_iff]
    constructor
    · intro hInd
      let K : Set (α ⊕ α) := (Sum.inl '' (I ∩ L)) ∪ (Sum.inr '' (I \ L))
      refine ⟨K, ?_, ?_⟩
      · apply (Matroid.sum_indep_iff _ _).mpr
        have hK₁ : Sum.inl ⁻¹' K = I ∩ L := by
          simp [K, Set.preimage_image_eq _ Sum.inl_injective]
        have hK₂ : Sum.inr ⁻¹' K = I \ L := by
          simp [K, Set.preimage_image_eq _ Sum.inr_injective]
        rw [hK₁, hK₂, Matroid.restrict_indep_iff, Matroid.restrict_indep_iff]
        constructor
        · exact ⟨hInd.subset Set.inter_subset_left, fun _ hx => ⟨hI hx.1, hx.2⟩⟩
        · exact ⟨hInd.subset Set.sdiff_subset, fun _ hx => ⟨hI hx.1, hx.2⟩⟩
      · rw [show joinSides '' K = I ∩ L ∪ (I \ L) from joinSides_image _ _]
        tauto_set
    · rintro ⟨K, hK, rfl⟩
      obtain ⟨hK₁, hK₂⟩ := (Matroid.sum_indep_iff _ _).mp hK
      rw [Matroid.restrict_indep_iff] at hK₁ hK₂
      apply h hI
      · apply hK₁.1.subset
        rintro x ⟨⟨k, hk, rfl⟩, hL⟩
        cases k with
        | inl k => exact hk
        | inr k => exact ((hK₂.2 hk).2 hL).elim
      · apply hK₂.1.subset
        rintro x ⟨⟨k, hk, rfl⟩, hL⟩
        cases k with
        | inl k => exact (hL (hK₁.2 hk).2).elim
        | inr k => exact hk

/-- Both positive ranks across a splitting cut force the top correction to vanish. -/
theorem SplitsAt.tau_eq_zero [Finite α] {M : Matroid α} {L : Set α} (h : SplitsAt M L)
    (h₁ : 0 < (M ↾ (M.E ∩ L)).eRank.toNat) (h₂ : 0 < (M ↾ (M.E \ L)).eRank.toNat) :
    tau M = 0 := by
  conv_lhs => rw [eq_map_sum_of_splitsAt M L h]
  rw [tau_map]
  exact tau_sum_eq_zero _ _ h₁ h₂

#print axioms splitsAt_of_baseSplice
#print axioms SplitsAt.contract
#print axioms SplitsAt.tau_eq_zero

end OpenMathResearch.MatroidKL
