import Mathlib.Basic.Finite.Sum
import Mathlib.Combinatorics.Matroid.Sum
import OpenMathResearch.MatroidFlatContract
import OpenMathResearch.MatroidKLProduct

/-!
# Direct sums and the Kazhdan–Lusztig top coefficient

The ranked flat poset of `M.sum N` is the product of the two ranked flat
posets. Consequently the Kazhdan–Lusztig polynomial is multiplicative and
its top admissible coefficient vanishes for two positive-rank summands
when their total rank is odd.
-/

open Set Matroid Polynomial
open scoped Polynomial

noncomputable section

namespace OpenMathResearch.MatroidKL

variable {α β : Type*} {M : Matroid α} {N : Matroid β}

@[simp] private theorem preimage_inl_image_self (X : Set α) :
    (@Sum.inl α β) ⁻¹' ((@Sum.inl α β) '' X) = X :=
  Set.preimage_image_eq X Sum.inl_injective

@[simp] private theorem preimage_inr_image_self (Y : Set β) :
    (@Sum.inr α β) ⁻¹' ((@Sum.inr α β) '' Y) = Y :=
  Set.preimage_image_eq Y Sum.inr_injective

private theorem sum_isFlat_iff {F : Set (α ⊕ β)} :
    (M.sum N).IsFlat F ↔ M.IsFlat (Sum.inl ⁻¹' F) ∧ N.IsFlat (Sum.inr ⁻¹' F) := by
  constructor
  · intro hF
    have hL : Sum.inl ⁻¹' F ⊆ M.E := by
      intro e he
      simpa [Matroid.sum_ground] using hF.subset_ground he
    have hR : Sum.inr ⁻¹' F ⊆ N.E := by
      intro e he
      simpa [Matroid.sum_ground] using hF.subset_ground he
    constructor
    · refine ⟨?_, hL⟩
      intro I X hIF hIX e he
      obtain ⟨J, hJ⟩ := N.exists_isBasis (Sum.inr ⁻¹' F) hR
      have h₁ : (M.sum N).IsBasis ((Sum.inl '' I) ∪ (Sum.inr '' J)) F := by
        simpa [Matroid.sum_isBasis_iff] using And.intro hIF hJ
      have h₂ : (M.sum N).IsBasis ((Sum.inl '' I) ∪ (Sum.inr '' J))
          ((Sum.inl '' X) ∪ (Sum.inr '' (Sum.inr ⁻¹' F))) := by
        simpa [Matroid.sum_isBasis_iff] using And.intro hIX hJ
      exact hF.subset_of_isBasis_of_isBasis h₁ h₂ (Or.inl ⟨e, he, rfl⟩)
    · refine ⟨?_, hR⟩
      intro J Y hJF hJY e he
      obtain ⟨I, hI⟩ := M.exists_isBasis (Sum.inl ⁻¹' F) hL
      have h₁ : (M.sum N).IsBasis ((Sum.inl '' I) ∪ (Sum.inr '' J)) F := by
        simpa [Matroid.sum_isBasis_iff] using And.intro hI hJF
      have h₂ : (M.sum N).IsBasis ((Sum.inl '' I) ∪ (Sum.inr '' J))
          ((Sum.inl '' (Sum.inl ⁻¹' F)) ∪ (Sum.inr '' Y)) := by
        simpa [Matroid.sum_isBasis_iff] using And.intro hI hJY
      exact hF.subset_of_isBasis_of_isBasis h₁ h₂ (Or.inr ⟨e, he, rfl⟩)
  · rintro ⟨hL, hR⟩
    constructor
    · intro I X hIF hIX e he
      have hIF' := Matroid.sum_isBasis_iff.mp hIF
      have hIX' := Matroid.sum_isBasis_iff.mp hIX
      cases e with
      | inl e => exact hL.subset_of_isBasis_of_isBasis hIF'.1 hIX'.1 he
      | inr e => exact hR.subset_of_isBasis_of_isBasis hIF'.2 hIX'.2 he
    · intro e he
      rw [Matroid.sum_ground]
      cases e with
      | inl e => exact Or.inl ⟨e, hL.subset_ground he, rfl⟩
      | inr e => exact Or.inr ⟨e, hR.subset_ground he, rfl⟩

/-- The flat poset of a disjoint-type direct sum is the product of the flat posets. -/
def flatSumIso (M : Matroid α) (N : Matroid β) : Flat (M.sum N) ≃o Flat M × Flat N where
  toFun F := (⟨Sum.inl ⁻¹' F.val, (sum_isFlat_iff.mp F.property).1⟩,
    ⟨Sum.inr ⁻¹' F.val, (sum_isFlat_iff.mp F.property).2⟩)
  invFun F := ⟨(Sum.inl '' F.1.val) ∪ (Sum.inr '' F.2.val),
    sum_isFlat_iff.mpr (by simpa using And.intro F.1.property F.2.property)⟩
  left_inv F := by
    apply Subtype.ext
    ext e
    cases e <;> simp
  right_inv F := by
    apply Prod.ext <;> apply Subtype.ext <;> simp
  map_rel_iff' := by
    intro F G
    change (Sum.inl ⁻¹' F.val ⊆ Sum.inl ⁻¹' G.val ∧ Sum.inr ⁻¹' F.val ⊆ Sum.inr ⁻¹' G.val) ↔
      F.val ⊆ G.val
    constructor
    · rintro ⟨h₁, h₂⟩ (e | e) he
      · exact h₁ he
      · exact h₂ he
    · exact fun h => ⟨preimage_mono h, preimage_mono h⟩

/-- Matroid rank is additive in the two coordinates of the flat-poset product. -/
theorem flatRank_sum [Finite α] [Finite β] (M : Matroid α) (N : Matroid β)
    (F : Flat (M.sum N)) :
    flatRank (M.sum N) F = flatRank M (flatSumIso M N F).1 + flatRank N (flatSumIso M N F).2 := by
  obtain ⟨I, hI⟩ := (M.sum N).exists_isBasis F.val F.property.subset_ground
  have h := Matroid.sum_isBasis_iff.mp hI
  change ((M.sum N).eRk F.val).toNat = (M.eRk (Sum.inl ⁻¹' F.val)).toNat +
    (N.eRk (Sum.inr ⁻¹' F.val)).toNat
  rw [← hI.encard_eq_eRk, ← h.1.encard_eq_eRk, ← h.2.encard_eq_eRk]
  let L : Set (α ⊕ β) := Sum.inl '' (Sum.inl ⁻¹' I)
  let R : Set (α ⊕ β) := Sum.inr '' (Sum.inr ⁻¹' I)
  change I.ncard = (Sum.inl ⁻¹' I).ncard + (Sum.inr ⁻¹' I).ncard
  have hSplit : L ∪ R = I := by
    ext e
    cases e <;> simp [L, R]
  have hDisj : Disjoint L R := by
    rw [Set.disjoint_left]
    rintro _ ⟨e, _, rfl⟩ ⟨f, _, hf⟩
    cases hf
  calc
    I.ncard = (L ∪ R).ncard := congrArg Set.ncard hSplit.symm
    _ = L.ncard + R.ncard := Set.ncard_union_eq hDisj
    _ = _ := by
      rw [Set.ncard_image_of_injective _ Sum.inl_injective,
        Set.ncard_image_of_injective _ Sum.inr_injective]

theorem rank_sum [Finite α] [Finite β] (M : Matroid α) (N : Matroid β) :
    (M.sum N).eRank.toNat = M.eRank.toNat + N.eRank.toNat := by
  simpa using flatRank_sum M N ⊤

/-- Kazhdan–Lusztig polynomials multiply on direct sums of finite matroids. -/
theorem matroidKL_sum [Finite α] [Finite β] (M : Matroid α) (N : Matroid β) :
    matroidKL (M.sum N) = matroidKL M * matroidKL N := by
  letI : LocallyFiniteOrder (Flat M × Flat N) := LocallyFiniteOrder.ofFiniteIcc fun _ _ => Set.toFinite _
  let e := flatSumIso M N
  have hM : IsKLFamily (flatRank M) (fun a i => (flatKL M a).coeff i) := by
    simpa only [coeff_flatKL] using flatKLCoeff_isKLFamily M
  have hN : IsKLFamily (flatRank N) (fun a i => (flatKL N a).coeff i) := by
    simpa only [coeff_flatKL] using flatKLCoeff_isKLFamily N
  have hProd := IsKLFamily.product (flatRank M) (flatRank N)
    (strictMono_flatRank M) (strictMono_flatRank N) (flatKL M) (flatKL N) hM hN
  have hFamily := hProd.comp_orderEmbedding _ (flatRank (M.sum N)) e.toOrderEmbedding
    (fun _ b _ => ⟨e.symm b, e.apply_symm_apply b⟩) e.map_top 0
    (fun F => by simpa [e, productRank] using (flatRank_sum M N F).symm)
  have hEq := hFamily.eq_klCoeff _ (strictMono_flatRank (M.sum N))
  ext i
  have h := congrFun (congrFun hEq (⊥ : Flat (M.sum N))) i
  change (flatKL M (e ⊥).1 * flatKL N (e ⊥).2).coeff i = flatKLCoeff (M.sum N) ⊥ i at h
  rw [e.map_bot] at h
  simpa [matroidKL] using h.symm

/-- The top admissible KL coefficient for odd rank, with value zero in even rank. -/
def tau [Finite α] (M : Matroid α) : ℤ :=
  if M.eRank.toNat % 2 = 1 then (matroidKL M).coeff ((M.eRank.toNat - 1) / 2) else 0

private theorem matroidKL_twice_natDegree_lt [Finite α] (M : Matroid α) (h : 0 < M.eRank.toNat) :
    2 * (matroidKL M).natDegree < M.eRank.toNat := by
  have hFamily : IsKLFamily (flatRank M) (fun a i => (flatKL M a).coeff i) := by
    simpa only [coeff_flatKL] using flatKLCoeff_isKLFamily M
  simpa [matroidKL, height] using hFamily.twice_natDegree_lt (flatRank M) (flatKL M) ⊥
    (by simpa [height] using h)

/-- The deletion correction vanishes on a direct sum of positive-rank matroids. -/
theorem tau_sum_eq_zero [Finite α] [Finite β] (M : Matroid α) (N : Matroid β)
    (hM : 0 < M.eRank.toNat) (hN : 0 < N.eRank.toNat) : tau (M.sum N) = 0 := by
  rw [tau, rank_sum, matroidKL_sum]
  split
  · have hDeg : (matroidKL M * matroidKL N).natDegree ≤ (matroidKL M).natDegree + (matroidKL N).natDegree :=
      Polynomial.natDegree_mul_le
    have h1 := matroidKL_twice_natDegree_lt M hM
    have h2 := matroidKL_twice_natDegree_lt N hN
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  · rfl

#print axioms flatRank_sum
#print axioms rank_sum
#print axioms matroidKL_sum
#print axioms tau_sum_eq_zero

end OpenMathResearch.MatroidKL
