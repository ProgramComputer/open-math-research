import OpenMathResearch.MatroidFlatDelete
import OpenMathResearch.MatroidKLSeparation

/-!
# Deletion across a splitting cut

Two closure witnesses force positive ranks in the required contracted pieces. The top-coefficient vanishing then gives the deletion identity.
-/

open Set Matroid

noncomputable section

namespace OpenMathResearch.MatroidKL

variable {α : Type*}

private theorem natRank_pos_of_nonloop [Finite α] {M : Matroid α} {x : α} (hx : M.IsNonloop x) :
    0 < M.eRank.toNat := by
  have hRank := M.eRk_le_eRank {x}
  have hOne : M.eRk {x} = 1 := by
    rw [hx.indep.eRk_eq_encard, Set.encard_singleton]
  rw [hOne] at hRank
  have hlt : M.eRank < ⊤ := M.eRank_le_encard_ground.trans_lt (Set.toFinite M.E).encard_lt_top
  exact ENat.toNat_le_toNat hRank hlt.ne

private theorem exists_nonloop_after_contract {M : Matroid α} {e : α} (F : Flat M)
    (hFlat : M.IsFlat (F.val \ {e})) {A : Set α} (hA : A ⊆ M.E \ {e}) (hCl : e ∈ M.closure A) :
    ∃ x ∈ A, (M ／ F.val).IsNonloop x := by
  have hNe : ¬ A ⊆ F.val := by
    intro hSub
    have hMeet : A ⊆ F.val \ {e} := fun x hx => ⟨hSub hx, (hA hx).2⟩
    have he := M.closure_mono hMeet hCl
    rw [hFlat.closure] at he
    exact he.2 (Set.mem_singleton e)
  obtain ⟨x, hxA, hxF⟩ := Set.not_subset.mp hNe
  refine ⟨x, hxA, Matroid.contract_isNonloop_iff.mpr ?_⟩
  rw [F.property.closure]
  exact ⟨(hA hxA).1, hxF⟩

/-- The cut gives deletion invariance when both sides contain a closure witness for the element. -/
theorem matroidZ_delete_of_split [Finite α] (M : Matroid α) (e : α) (L A B : Set α)
    (hSpan : M.Spanning (M.E \ {e})) (hSplit : SplitsAt (M ／ ({e} : Set α)) L)
    (hA : A ⊆ M.E \ {e}) (hAL : A ⊆ L) (hAcl : e ∈ M.closure A)
    (hB : B ⊆ M.E \ {e}) (hBR : Disjoint B L) (hBcl : e ∈ M.closure B) :
    matroidZ M = matroidZ (M ＼ {e}) := by
  apply matroidZ_delete_of_tau_zero M e hSpan
  intro F heF hFlat
  have hUnion : ({e} : Set α) ∪ (F.val \ {e}) = F.val := by
    have hSub : ({e} : Set α) ⊆ F.val := Set.singleton_subset_iff.mpr heF
    tauto_set
  have hCut : SplitsAt (M ／ F.val) L := by
    simpa only [Matroid.contract_contract, hUnion] using hSplit.contract (F.val \ {e})
  obtain ⟨x, hxA, hx⟩ := exists_nonloop_after_contract F hFlat hA hAcl
  obtain ⟨y, hyB, hy⟩ := exists_nonloop_after_contract F hFlat hB hBcl
  apply hCut.tau_eq_zero
  · apply natRank_pos_of_nonloop
    exact Matroid.restrict_isNonloop_iff.mpr ⟨hx, hx.mem_ground, hAL hxA⟩
  · apply natRank_pos_of_nonloop
    exact Matroid.restrict_isNonloop_iff.mpr ⟨hy, hy.mem_ground, (Set.disjoint_left.mp hBR) hyB⟩

#print axioms matroidZ_delete_of_split

end OpenMathResearch.MatroidKL
