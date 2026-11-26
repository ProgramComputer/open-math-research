import Mathlib.Combinatorics.Matroid.Minor.Delete
import OpenMathResearch.MatroidFlatSum
import OpenMathResearch.MatroidKLDeletionProfile

/-!
# Matroid deletion when the Kazhdan–Lusztig correction vanishes

A deletion flat lifts to its closure in the original matroid. This gives
an adjunction for the flat posets, preserves rank on the lift, and leaves
at most one unit of discrepancy in the reverse direction. The coefficient
pushforward proves the Z-polynomial equality once the specified
contractions have vanishing top Kazhdan–Lusztig coefficient.
-/

open Set Matroid Polynomial
open scoped Polynomial

noncomputable section

namespace OpenMathResearch.MatroidKL

variable {α : Type*}

/-- Remove one element from a flat, viewed as a flat of the deletion. -/
def deleteFlat (M : Matroid α) (e : α) (F : Flat M) : Flat (M ＼ {e}) := by
  refine ⟨F.val \ {e}, Matroid.isFlat_iff_closure_eq.mpr ?_⟩
  rw [Matroid.delete_closure_eq]
  have hSubset : (F.val \ {e}) \ {e} ⊆ F.val := Set.diff_subset.trans Set.diff_subset
  have hCl : M.closure ((F.val \ {e}) \ {e}) ⊆ F.val :=
    (M.closure_mono hSubset).trans F.property.closure.subset
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨hCl hx.1, hx.2⟩
  · intro x hx
    exact ⟨M.subset_closure _ (hSubset.trans F.property.subset_ground) ⟨hx, hx.2⟩, hx.2⟩

/-- The least flat of the original matroid that restricts to a prescribed deletion flat. -/
def liftDeletionFlat (M : Matroid α) (e : α) (K : Flat (M ＼ {e})) : Flat M :=
  ⟨M.closure K.val, M.isFlat_closure (X := K.val)⟩

theorem deletionFlat_adj (M : Matroid α) (e : α) (F : Flat M) (K : Flat (M ＼ {e})) :
    K ≤ deleteFlat M e F ↔ liftDeletionFlat M e K ≤ F := by
  change K.val ⊆ F.val \ {e} ↔ M.closure K.val ⊆ F.val
  constructor
  · intro h
    rw [← F.property.closure]
    exact M.closure_mono (h.trans Set.diff_subset)
  · intro h x hx
    have hK : K.val ⊆ M.E := K.property.subset_ground.trans Set.diff_subset
    exact ⟨h (M.subset_closure _ hK hx), (K.property.subset_ground hx).2⟩

@[simp] theorem deleteFlat_top (M : Matroid α) (e : α) : deleteFlat M e ⊤ = ⊤ := by
  apply Subtype.ext
  exact (M.delete_ground {e}).symm

private theorem eRk_delete_subset (M : Matroid α) (e : α) {X : Set α} (h : X ⊆ (M ＼ {e}).E) :
    (M ＼ {e}).eRk X = M.eRk X := by
  change X ⊆ M.E \ {e} at h
  rw [Matroid.delete_eq_restrict, M.restrict_eRk_eq h]

theorem flatRank_liftDeletionFlat (M : Matroid α) (e : α) (K : Flat (M ＼ {e})) :
    flatRank M (liftDeletionFlat M e K) = flatRank (M ＼ {e}) K := by
  change (M.eRk (M.closure K.val)).toNat = ((M ＼ {e}).eRk K.val).toNat
  rw [M.eRk_closure_eq, eRk_delete_subset M e K.property.subset_ground]

private theorem natRank_mono [Finite α] (M : Matroid α) {X Y : Set α} (h : X ⊆ Y) :
    (M.eRk X).toNat ≤ (M.eRk Y).toNat :=
  ENat.toNat_le_toNat (M.eRk_mono h) ((M.eRk_le_encard Y).trans_lt ((Set.toFinite Y).encard_lt_top)).ne

theorem flatRank_deleteFlat_gap [Finite α] (M : Matroid α) (e : α) (F : Flat M) :
    flatRank (M ＼ {e}) (deleteFlat M e F) ≤ flatRank M F ∧
      flatRank M F ≤ flatRank (M ＼ {e}) (deleteFlat M e F) + 1 := by
  change ((M ＼ {e}).eRk (F.val \ {e})).toNat ≤ (M.eRk F.val).toNat ∧
    (M.eRk F.val).toNat ≤ ((M ＼ {e}).eRk (F.val \ {e})).toNat + 1
  have hSub : F.val \ {e} ⊆ (M ＼ {e}).E := by
    rw [M.delete_ground]
    exact Set.sdiff_subset_sdiff_left F.property.subset_ground
  rw [eRk_delete_subset M e hSub]
  refine ⟨natRank_mono M Set.diff_subset, ?_⟩
  obtain ⟨I, hI⟩ := M.exists_isBasis F.val F.property.subset_ground
  have hIndep : M.Indep (I \ {e}) := hI.indep.subset Set.diff_subset
  have hLe := natRank_mono M (Set.sdiff_subset_sdiff_left (t := ({e} : Set α)) hI.subset)
  rw [hIndep.eRk_eq_encard] at hLe
  rw [← hI.encard_eq_eRk]
  have hc := Set.pred_ncard_le_ncard_sdiff_singleton I e
  change (I \ {e}).ncard ≤ (M.eRk (F.val \ {e})).toNat at hLe
  change I.ncard ≤ (M.eRk (F.val \ {e})).toNat + 1
  omega

/-- Discrepancy one means the element was present and its removal leaves another original flat. -/
theorem deleteFlat_discrepancy_one [Finite α] (M : Matroid α) (e : α) (F : Flat M)
    (h : flatRank M F = flatRank (M ＼ {e}) (deleteFlat M e F) + 1) :
    e ∈ F.val ∧ M.IsFlat (F.val \ {e}) := by
  have hSub : F.val \ {e} ⊆ (M ＼ {e}).E := by
    rw [M.delete_ground]
    exact Set.sdiff_subset_sdiff_left F.property.subset_ground
  change (M.eRk F.val).toNat = ((M ＼ {e}).eRk (F.val \ {e})).toNat + 1 at h
  rw [eRk_delete_subset M e hSub] at h
  have he : e ∈ F.val := by
    by_contra he
    have hs : F.val \ {e} = F.val := by
      refine Set.Subset.antisymm Set.diff_subset ?_
      intro x hx
      exact ⟨hx, fun hxE => he ((Set.mem_singleton_iff.mp hxE) ▸ hx)⟩
    rw [hs] at h
    omega
  refine ⟨he, Matroid.isFlat_iff_closure_eq.mpr ?_⟩
  have hf : M.closure (F.val \ {e}) ⊆ F.val :=
    (M.closure_mono Set.diff_subset).trans F.property.closure.subset
  have hne : e ∉ M.closure (F.val \ {e}) := by
    intro heCl
    have hF : F.val ⊆ M.closure (F.val \ {e}) := by
      intro x hx
      by_cases hxe : x = e
      · simpa only [hxe] using heCl
      · exact M.subset_closure _ (Set.diff_subset.trans F.property.subset_ground)
          ⟨hx, by simpa using hxe⟩
    have hRank := natRank_mono M hF
    rw [M.eRk_closure_eq] at hRank
    omega
  apply Set.Subset.antisymm
  · exact fun x hx => ⟨hf hx, by simpa using fun he : x = e => hne (he ▸ hx)⟩
  · exact M.subset_closure _ (Set.diff_subset.trans F.property.subset_ground)

private theorem flatRank_top_eq_delete [Finite α] (M : Matroid α) (e : α)
    (hSpan : M.Spanning (M.E \ {e})) : flatRank M ⊤ = flatRank (M ＼ {e}) ⊤ := by
  change (M.eRk M.E).toNat = ((M ＼ {e}).eRk (M.E \ {e})).toNat
  rw [eRk_delete_subset M e (by rw [M.delete_ground]),
    ← M.eRk_closure_eq (M.E \ {e}), hSpan.closure_eq_of_superset (Set.Subset.rfl)]

private theorem centeredCoeff_eq_tau_contract [Finite α] (M : Matroid α) (F : Flat M) :
    centeredCoeff (height (flatRank M) F) (flatKL M F) 1 = tau (M ／ F.val) := by
  have hR := flatRank_contractFlatEmbedding F (⊤ : Flat (M ／ F.val))
  rw [contractFlatEmbedding_top, flatRank_top, flatRank_top] at hR
  have hH : height (flatRank M) F = (M ／ F.val).eRank.toNat := by
    unfold height
    rw [flatRank_top]
    omega
  have hP := flatKL_contract F (⊥ : Flat (M ／ F.val))
  rw [contractFlatEmbedding_bot] at hP
  rw [hH, hP, centeredCoeff_one, tau, matroidKL]

/-- Deleting a spanning-complement element preserves Z when all the prescribed corrections are zero. -/
theorem matroidZ_delete_of_tau_zero [Finite α] (M : Matroid α) (e : α)
    (hSpan : M.Spanning (M.E \ {e}))
    (hTau : ∀ F : Flat M, e ∈ F.val → M.IsFlat (F.val \ {e}) → tau (M ／ F.val) = 0) :
    matroidZ M = matroidZ (M ＼ {e}) := by
  have hSum (P : Matroid α) : matroidZ P = shiftedSum (flatRank P) (flatKL P) ⊥ := by
    ext k
    simp [coeff_shiftedSum, matroidZCoeff]
  rw [hSum M, hSum (M ＼ {e})]
  apply shiftedSum_eq_of_deletionPush (flatRank M) (flatRank (M ＼ {e}))
    (strictMono_flatRank M) (strictMono_flatRank _) (deleteFlat M e) (liftDeletionFlat M e)
    (deletionFlat_adj M e) (flatRank_liftDeletionFlat M e) (deleteFlat_top M e)
    (flatRank_top_eq_delete M e hSpan) (flatRank_deleteFlat_gap M e)
  · simpa only [coeff_flatKL] using flatKLCoeff_isKLFamily M
  · simpa only [coeff_flatKL] using flatKLCoeff_isKLFamily (M ＼ {e})
  · intro F hDisc
    obtain ⟨he, hFlat⟩ := deleteFlat_discrepancy_one M e F hDisc
    rw [centeredCoeff_eq_tau_contract, hTau F he hFlat]

/-- A parallel copy can be deleted while preserving the Z-polynomial. -/
theorem matroidZ_delete_of_parallel [Finite α] (M : Matroid α) {e f : α}
    (hef : e ≠ f) (he : e ∈ M.closure {f}) (hf : f ∈ M.closure {e}) :
    matroidZ M = matroidZ (M ＼ {e}) := by
  have hfG : f ∈ M.E \ {e} := ⟨M.closure_subset_ground _ hf, by simpa using Ne.symm hef⟩
  have heG : e ∈ M.closure (M.E \ {e}) := M.closure_mono (Set.singleton_subset_iff.mpr hfG) he
  have hSp : M.Spanning (M.E \ {e}) := by
    apply (Matroid.spanning_iff_closure_eq (show M.E \ {e} ⊆ M.E from Set.diff_subset)).mpr
    apply Set.Subset.antisymm (M.closure_subset_ground _)
    intro x hx
    by_cases hxe : x = e
    · simpa only [hxe] using heG
    · exact M.subset_closure _ Set.diff_subset ⟨hx, by simpa using hxe⟩
  apply matroidZ_delete_of_tau_zero M e hSp
  intro F heF hFlat
  have hfF : f ∈ F.val := by
    have hfCl := M.closure_mono (Set.singleton_subset_iff.mpr heF) hf
    rwa [F.property.closure] at hfCl
  have hfDel : f ∈ F.val \ {e} := ⟨hfF, by simpa using Ne.symm hef⟩
  have heDel := M.closure_mono (Set.singleton_subset_iff.mpr hfDel) he
  rw [hFlat.closure] at heDel
  exact (heDel.2 (Set.mem_singleton e)).elim

#print axioms deletionFlat_adj
#print axioms flatRank_liftDeletionFlat
#print axioms flatRank_deleteFlat_gap
#print axioms deleteFlat_discrepancy_one
#print axioms matroidZ_delete_of_tau_zero
#print axioms matroidZ_delete_of_parallel

end OpenMathResearch.MatroidKL
