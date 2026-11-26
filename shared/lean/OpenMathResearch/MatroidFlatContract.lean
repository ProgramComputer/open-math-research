import Mathlib.Combinatorics.Matroid.Minor.Contract
import OpenMathResearch.MatroidFlatPolynomial

/-!
# The ranked flat interval of a contraction

For a flat `F` of `M`, adjoining `F` identifies each flat of `M ／ F` with a
flat of `M` above `F`, and shifts the rank by the rank of `F`.
-/

open Set Matroid Polynomial
open scoped BigOperators Polynomial

noncomputable section

namespace OpenMathResearch.MatroidKL

variable {α : Type*} {M : Matroid α}

private theorem contractFlat_disjoint (F : Flat M) (H : Flat (M ／ F.val)) :
    Disjoint H.val F.val := by
  rw [Set.disjoint_left]
  exact fun _ he => (H.property.subset_ground he).2

/-- Adjoin the contracted flat to a flat of the contraction. -/
def liftContractFlat (F : Flat M) (H : Flat (M ／ F.val)) : Flat M := by
  refine ⟨H.val ∪ F.val, Matroid.isFlat_iff_closure_eq.mpr ?_⟩
  have hc := H.property.closure
  rw [Matroid.contract_closure_eq] at hc
  apply Set.Subset.antisymm
  · intro e he
    by_cases heF : e ∈ F.val
    · exact Or.inr heF
    · exact Or.inl (hc ▸ ⟨he, heF⟩)
  · exact M.subset_closure _ (union_subset
      (H.property.subset_ground.trans (M.contract_ground_subset_ground _)) F.property.subset_ground)

/-- Delete the contracted flat from a flat above it. -/
def lowerContractFlat (F G : Flat M) (hFG : F ≤ G) : Flat (M ／ F.val) := by
  refine ⟨G.val \ F.val, Matroid.isFlat_iff_closure_eq.mpr ?_⟩
  have hs : (G.val \ F.val) ∪ F.val = G.val := by
    change F.val ⊆ G.val at hFG
    tauto_set
  rw [Matroid.contract_closure_eq, hs, G.property.closure]

/-- The coordinate map from contraction flats to the upper interval above `F`. -/
def contractFlatEmbedding (F : Flat M) : Flat (M ／ F.val) ↪o Flat M where
  toFun := liftContractFlat F
  inj' := by
    intro H K h
    have he := congrArg Subtype.val h
    change H.val ∪ F.val = K.val ∪ F.val at he
    have hH := contractFlat_disjoint F H
    have hK := contractFlat_disjoint F K
    apply Subtype.ext
    rw [Set.disjoint_left] at hH hK
    tauto_set
  map_rel_iff' := by
    intro H K
    change H.val ∪ F.val ⊆ K.val ∪ F.val ↔ H.val ⊆ K.val
    constructor
    · intro h e he
      exact (h (Or.inl he)).resolve_right (Set.disjoint_left.mp (contractFlat_disjoint F H) he)
    · exact fun h => union_subset_union_left _ h

theorem contractFlatEmbedding_exists (F G : Flat M) (hFG : F ≤ G) :
    ∃ H : Flat (M ／ F.val), contractFlatEmbedding F H = G := by
  refine ⟨lowerContractFlat F G hFG, Subtype.ext ?_⟩
  change (G.val \ F.val) ∪ F.val = G.val
  change F.val ⊆ G.val at hFG
  tauto_set

@[simp] theorem contractFlatEmbedding_top (F : Flat M) :
    contractFlatEmbedding F ⊤ = ⊤ := by
  apply Subtype.ext
  change (M.E \ F.val) ∪ F.val = M.E
  have hF := F.property.subset_ground
  tauto_set

@[simp] theorem contractFlatEmbedding_bot (F : Flat M) :
    contractFlatEmbedding F ⊥ = F := by
  apply Subtype.ext
  change (M ／ F.val).closure ∅ ∪ F.val = F.val
  rw [Matroid.contract_closure_eq, empty_union, F.property.closure]
  simp

/-- Rank on the upper interval is the contraction rank plus the contracted rank. -/
theorem flatRank_contractFlatEmbedding [Finite α] (F : Flat M) (H : Flat (M ／ F.val)) :
    flatRank M (contractFlatEmbedding F H) = flatRank M F + flatRank (M ／ F.val) H := by
  obtain ⟨I, hI⟩ := M.exists_isBasis F.val F.property.subset_ground
  obtain ⟨J, hJ⟩ := (M ／ F.val).exists_isBasis H.val H.property.subset_ground
  have hIJ := hI.contract_indep_iff.mp hJ.indep
  have hH : H.val ⊆ M.closure (J ∪ I) := by
    have h : H.val ⊆ (M ／ F.val).closure J := by
      rw [hJ.closure_eq_closure, H.property.closure]
    rw [Matroid.contract_closure_eq, Matroid.closure_union_congr_right hI.closure_eq_closure.symm] at h
    exact h.trans Set.diff_subset
  have hF : F.val ⊆ M.closure (J ∪ I) := by
    apply Set.Subset.trans _ (M.closure_mono subset_union_right)
    rw [hI.closure_eq_closure, F.property.closure]
  have hb := hIJ.1.isBasis_of_subset_of_subset_closure
    (union_subset_union hJ.subset hI.subset) (union_subset hH hF)
  have hDisj : Disjoint J I := hIJ.2.symm.mono_right hI.subset
  change (M.eRk (H.val ∪ F.val)).toNat = (M.eRk F.val).toNat + ((M ／ F.val).eRk H.val).toNat
  rw [← hb.encard_eq_eRk, ← hI.encard_eq_eRk, ← hJ.encard_eq_eRk]
  exact (Set.ncard_union_eq hDisj).trans (Nat.add_comm _ _)

/-- The polynomial indexed by a flat `F` is the bottom-interval KL polynomial of `M ／ F`. -/
theorem flatKL_contract [Finite α] (F : Flat M) (H : Flat (M ／ F.val)) :
    flatKL M (contractFlatEmbedding F H) = flatKL (M ／ F.val) H := by
  have h := (flatKLCoeff_isKLFamily M).comp_orderEmbedding (flatRank M) (flatRank (M ／ F.val))
    (contractFlatEmbedding F) (fun a b hab => contractFlatEmbedding_exists F b
      (show F ≤ b from (show F.val ⊆ (contractFlatEmbedding F a).val from subset_union_right).trans hab))
    (contractFlatEmbedding_top F) (flatRank M F) (flatRank_contractFlatEmbedding F)
  have he := h.eq_klCoeff (flatRank (M ／ F.val)) (strictMono_flatRank (M ／ F.val))
  ext i
  rw [coeff_flatKL, coeff_flatKL]
  exact congrFun (congrFun he H) i

/-- The Kazhdan–Lusztig polynomial of the whole finite matroid. -/
def matroidKL [Finite α] (M : Matroid α) : ℤ[X] := flatKL M ⊥

/-- The Z-polynomial is the sum of the shifted KL polynomials of the contractions. -/
theorem matroidZ_eq_sum_contract [Finite α] (M : Matroid α) :
    matroidZ M = ∑ F : Flat M, X ^ flatRank M F * matroidKL (M ／ F.val) := by
  rw [matroidZ_eq_sum]
  apply Finset.sum_congr rfl
  intro F _
  have h := flatKL_contract F (⊥ : Flat (M ／ F.val))
  rw [contractFlatEmbedding_bot] at h
  rw [h]
  rfl

theorem matroidKL_of_rank_zero [Finite α] (M : Matroid α) (h : M.eRank.toNat = 0) :
    matroidKL M = 1 := by
  ext i
  rw [matroidKL, coeff_flatKL, (flatKLCoeff_isKLFamily M).rank_zero _ (by simp [height, h])]
  simp [Polynomial.coeff_one]

theorem matroidKL_coeff_eq_zero_of_high [Finite α] (M : Matroid α) (i : ℕ)
    (hRank : 0 < M.eRank.toNat) (hi : M.eRank.toNat ≤ 2 * i) : (matroidKL M).coeff i = 0 := by
  rw [matroidKL, coeff_flatKL]
  exact (flatKLCoeff_isKLFamily M).high_coeff _ _ (by simpa [height] using hRank)
    (by simpa [height] using hi)

/-- The original characteristic-polynomial recursion summed over the flats of the matroid. -/
theorem matroidKL_characteristicRecurrence [Finite α] (M : Matroid α) :
    (matroidKL M).reflect M.eRank.toNat =
      ∑ F : Flat M, intervalCharacteristic (flatRank M) ⊥ F * matroidKL (M ／ F.val) := by
  have hall : Finset.Icc (⊥ : Flat M) ⊤ = Finset.univ := by
    ext F
    simp
  have h := flatKL_characteristicRecurrence M ⊥
  simp only [height, flatRank_top, flatRank_bot, Nat.sub_zero, hall] at h
  rw [matroidKL, h]
  apply Finset.sum_congr rfl
  intro F _
  have he := flatKL_contract F (⊥ : Flat (M ／ F.val))
  rw [contractFlatEmbedding_bot] at he
  rw [he]
  rfl

#print axioms contractFlatEmbedding_exists
#print axioms contractFlatEmbedding_top
#print axioms contractFlatEmbedding_bot
#print axioms flatRank_contractFlatEmbedding
#print axioms flatKL_contract
#print axioms matroidZ_eq_sum_contract
#print axioms matroidKL_of_rank_zero
#print axioms matroidKL_coeff_eq_zero_of_high
#print axioms matroidKL_characteristicRecurrence

end OpenMathResearch.MatroidKL
