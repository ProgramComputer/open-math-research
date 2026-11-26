import OpenMathResearch.MatroidFlatSum

/-!
# Relabeling finite matroids

A relabeling injective on the ground set gives a rank-preserving order isomorphism of flat posets and preserves the Kazhdan–Lusztig polynomial.
-/

open Set Matroid Polynomial
open scoped Polynomial

noncomputable section

namespace OpenMathResearch.MatroidKL

variable {α β : Type*}

private theorem preimage_image_inter_ground (M : Matroid α) (f : α → β) (hf : InjOn f M.E)
    {F : Set α} (hF : F ⊆ M.E) : f ⁻¹' (f '' F) ∩ M.E = F := by
  ext a
  constructor
  · rintro ⟨⟨b, hb, hEq⟩, ha⟩
    exact (hf (hF hb) ha hEq) ▸ hb
  · intro ha
    exact ⟨⟨a, ha, rfl⟩, hF ha⟩

private theorem image_preimage_inter_ground (M : Matroid α) (f : α → β)
    {G : Set β} (hG : G ⊆ f '' M.E) : f '' (f ⁻¹' G ∩ M.E) = G := by
  ext b
  constructor
  · rintro ⟨a, ⟨ha, _⟩, rfl⟩
    exact ha
  · intro hb
    obtain ⟨a, ha, ha'⟩ := hG hb
    refine ⟨a, ⟨?_, ha⟩, ha'⟩
    change f a ∈ G
    rwa [ha']

private def mapFlat (M : Matroid α) (f : α → β) (hf : InjOn f M.E) (F : Flat M) : Flat (M.map f hf) := by
  refine ⟨f '' F.val, Matroid.isFlat_iff_closure_eq.mpr ?_⟩
  rw [Matroid.map_closure_eq, ← M.closure_inter_ground (f ⁻¹' (f '' F.val)),
    preimage_image_inter_ground M f hf F.property.subset_ground, F.property.closure]

private def pullFlat (M : Matroid α) (f : α → β) (hf : InjOn f M.E) (G : Flat (M.map f hf)) : Flat M := by
  refine ⟨f ⁻¹' G.val ∩ M.E, Matroid.isFlat_iff_closure_eq.mpr ?_⟩
  apply (hf.image_eq_image_iff (M.closure_subset_ground _) Set.inter_subset_right).mp
  rw [M.closure_inter_ground, ← M.map_closure_eq f hf G.val, G.property.closure,
    image_preimage_inter_ground M f G.property.subset_ground]

/-- Injective relabeling on the ground set identifies the ordered sets of flats. -/
def mapFlatIso (M : Matroid α) (f : α → β) (hf : InjOn f M.E) : Flat M ≃o Flat (M.map f hf) where
  toFun := mapFlat M f hf
  invFun := pullFlat M f hf
  left_inv F := Subtype.ext (preimage_image_inter_ground M f hf F.property.subset_ground)
  right_inv G := Subtype.ext (image_preimage_inter_ground M f G.property.subset_ground)
  map_rel_iff' := by
    intro F G
    change f '' F.val ⊆ f '' G.val ↔ F.val ⊆ G.val
    constructor
    · intro h a ha
      obtain ⟨b, hb, hEq⟩ := h ⟨a, ha, rfl⟩
      exact (hf (G.property.subset_ground hb) (F.property.subset_ground ha) hEq) ▸ hb
    · exact Set.image_mono

theorem flatRank_map (M : Matroid α) (f : α → β) (hf : InjOn f M.E) (F : Flat M) :
    flatRank (M.map f hf) (mapFlatIso M f hf F) = flatRank M F := by
  obtain ⟨I, hI⟩ := M.exists_isBasis F.val F.property.subset_ground
  change ((M.map f hf).eRk (f '' F.val)).toNat = (M.eRk F.val).toNat
  rw [← (hI.map hf).encard_eq_eRk, ← hI.encard_eq_eRk,
    (hf.mono hI.indep.subset_ground).encard_image]

theorem rank_map (M : Matroid α) (f : α → β) (hf : InjOn f M.E) :
    (M.map f hf).eRank.toNat = M.eRank.toNat := by
  simpa using flatRank_map M f hf ⊤

/-- A relabeling injective on the ground set preserves the whole KL polynomial. -/
theorem matroidKL_map [Finite α] [Finite β] (M : Matroid α) (f : α → β) (hf : InjOn f M.E) :
    matroidKL (M.map f hf) = matroidKL M := by
  let e := mapFlatIso M f hf
  have h := (flatKLCoeff_isKLFamily (M.map f hf)).comp_orderEmbedding
    (flatRank (M.map f hf)) (flatRank M) e.toOrderEmbedding (fun _ G _ => ⟨e.symm G, e.apply_symm_apply G⟩)
    e.map_top 0 (fun F => by simpa using flatRank_map M f hf F)
  have hEq := h.eq_klCoeff _ (strictMono_flatRank M)
  ext i
  have he := congrFun (congrFun hEq (⊥ : Flat M)) i
  change flatKLCoeff (M.map f hf) (e ⊥) i = flatKLCoeff M ⊥ i at he
  rw [e.map_bot] at he
  simpa [matroidKL] using he

theorem tau_map [Finite α] [Finite β] (M : Matroid α) (f : α → β) (hf : InjOn f M.E) :
    tau (M.map f hf) = tau M := by
  rw [tau, rank_map, matroidKL_map, tau]

#print axioms flatRank_map
#print axioms matroidKL_map
#print axioms tau_map

end OpenMathResearch.MatroidKL
